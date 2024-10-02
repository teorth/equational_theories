module Main where

import FiniteMagmaTools.Equation (Equation)
import qualified FiniteMagmaTools.Equation as Equation

import FiniteMagmaTools.Magma (Magma)
import qualified FiniteMagmaTools.Magma as Magma

import FiniteMagmaTools.Plan

import ParseMace4.ParseInterps (parseMace4)

import Data.List (intersperse)

import System.IO
import System.Environment (getArgs)

displayHelp :: IO ()
displayHelp =
  logger . concat . intersperse "\n" $
    [ "Usage: cabal exec parse-mace4 < input.txt > output.txt"
    , ""
    , "This script generates make-plan format lists from Mace4 magma outputs."
    , "The magma operation is assumed to be +, all other function symbols are"
    , "ignored. This helps if you want the operator tables of say all groups,"
    , "where other operations will be present."
    , ""
    , "The output format is the same as that of make-plan, but the Satisfies"
    , "and Refutes fields are left empty (you should use other tools for that)."
    ]

main :: IO ()
main = do
  args <- getArgs
  if "--help" `elem` args || "-h" `elem` args
    then displayHelp
    else do
      input <- getContents
      case parseMace4 input of
        Left err -> do
          logger "Parse Error"
          logger "-----------"
          logger err
        Right tables -> do
          let magmas = map Magma.fromTable tables
          let entries = [PlanEntry (Magma.name m) [] [] | m <- magmas]
          printPlan (Plan (-1) entries)

logger :: String -> IO ()
logger = hPutStrLn stderr
