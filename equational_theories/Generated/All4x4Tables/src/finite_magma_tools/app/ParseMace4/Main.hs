module Main where

import FiniteMagmaTools.Equation (Equation)
import qualified FiniteMagmaTools.Equation as Equation

import FiniteMagmaTools.Magma (Magma)
import qualified FiniteMagmaTools.Magma as Magma

import FiniteMagmaTools.Plan
import qualified FiniteMagmaTools.Evaluator as Evaluator

import ParseMace4.ParseInterps (parseMace4)

import Data.List (intersperse)

import System.IO
import System.Environment (getArgs)

import Options.Applicative

displayHelp :: IO ()
displayHelp =
  logger . concat . intersperse "\n" $
    [ "Usage: cabal exec parse-mace4 [-- -c FILE] < input.txt > output.txt"
    , ""
    , "This script generates make-plan format lists from Mace4 magma outputs."
    , "The magma operation is assumed to be +, all other function symbols are"
    , "ignored. This helps if you want the operator tables of say all groups,"
    , "where other operations will be present."
    , ""
    , "The output format is the same as that of make-plan, but the Satisfies"
    , "and Refutes fields are left empty (you should use other tools for that)."
    , "If -c /path/to/equations.txt is supplied, the tool determines which "
    , "equations are satisfied in the magmas and outputs All4x4Tables-style."
    ]

data Options = Options
  { checkEquations :: Maybe FilePath
  , showHelp :: Bool
  }

optionsParser :: Parser Options
optionsParser = Options
  <$> optional (strOption
        ( long "check-equations"
       <> short 'c'
       <> metavar "FILE"
       <> help "Check equations from FILE" ))
  <*> switch
        ( long "help"
       <> short 'h'
       <> help "Show help information" )

opts :: ParserInfo Options
opts = info (optionsParser <**> helper)
  ( fullDesc
  <> progDesc "Generates make-plan format lists from Mace4 magma outputs."
  <> header "parse-mace4 - a tool for parsing Mace4 magma outputs" )

chunkInputs :: [a] -> [(String, [a])]
chunkInputs = go 0 where
  go _ [] = []
  go start xs = (range, chunk) : go (start + 100) rest
    where
      (chunk, rest) = splitAt 100 xs
      range = show start ++ "-" ++ show (start + length chunk - 1)

processChunks :: (String -> [a] -> IO [b]) -> [a] -> IO [b]
processChunks action list = fmap concat $ mapM (uncurry action) (chunkInputs list)

main :: IO ()
main = do
  options <- execParser opts
  if showHelp options then displayHelp else do
    input <- getContents
    case parseMace4 input of
      Left err -> do
        logger "Parse Error"
        logger "-----------"
        logger err
      Right tables -> do
        let magmas = map Magma.fromTable tables
        case checkEquations options of
          Just filePath -> do
            -- checking equations, so we emit All4x4Tables output
            logger $ "Checking equations from: " ++ filePath
            equations <- readFile filePath
            let rels = Evaluator.parseRelations equations
            logger $ "Parsed " ++ show (length rels) ++ " equations."
            let
              createRecord m =
                let
                  res = Evaluator.satisfied rels m
                in
                  Magma.Record m res
              process range ms = do
                logger $ "process: handling magmas " ++ range ++ "."
                let result = map createRecord ms
                Magma.printRecords result
                return result
            processed <- processChunks process magmas
            logger $ "process: finished."
          Nothing -> do
            -- no need to check equations, we emit a plan
            let entries = [PlanEntry (Magma.name m) [] [] | m <- magmas]
            printPlan (Plan (-1) entries)

logger :: String -> IO ()
logger = hPutStrLn stderr
