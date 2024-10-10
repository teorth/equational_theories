module Main where

import FiniteMagmaTools.Equation (Equation)
import qualified FiniteMagmaTools.Equation as Equation

import FiniteMagmaTools.Magma (Magma)
import qualified FiniteMagmaTools.Magma as Magma

import FiniteMagmaTools.Plan
import FiniteMagmaTools.PlanParser

import Data.List (intersperse)

import System.IO
import System.Environment (getArgs)

displayHelp :: IO ()
displayHelp =
  logger . concat . intersperse "\n" $
    [ "Usage: cabal exec gen-refutations < in.txt"
    , ""
    , "This script generates Lean refutation files from the input plan."
    , "Output files are named Refutation<n>.lean, where <n> is the index of the"
    , "magma in the input plan."
    , ""
    , "The input format matches the output format of make-plan."
    ]

main :: IO ()
main = do
  args <- getArgs
  if "--help" `elem` args || "-h" `elem` args
    then displayHelp
    else do
      input <- getContents
      case parsePlan input of
        Left err -> do
          logger "Parse Error"
          logger "-----------"
          logger err
        Right plan -> processPlan plan

logger :: String -> IO ()
logger = hPutStrLn stderr

processPlan :: Plan -> IO ()
processPlan plan = do
  let n = length (planEntries plan) - 1
  let entries = planEntries plan
  let open x = openFile ("Refutation" ++ show x ++ ".lean") WriteMode
  handles <- mapM open [0..n]
  mapM_ (uncurry processEntry) (zip handles entries)
  mapM_ hClose handles

processEntry :: Handle -> PlanEntry -> IO ()
processEntry handle entry = do
  case maybeRead (peMagma entry) :: Maybe [[Int]] of
    Nothing -> do
      logger $ "processEntry: skipping bad magma " ++ show (peMagma entry) ++ "."
      hPutStrLn handle "/-!"
      hPutStrLn handle "This file was generated from the bad magma:"
      hPutStrLn handle (peMagma entry)
      hPutStrLn handle "-/"
    Just p -> do
      let magma = Magma.fromTable p
      let satisfied = peSatisfies entry
      let refuted = peRefutes entry
      emitImports handle
      emitComment handle magma
      emitDefinition handle magma
      emitFacts handle magma satisfied refuted

emitImports :: Handle -> IO ()
emitImports handle = do
  hPutStrLn handle "import equational_theories.Equations.All"
  hPutStrLn handle "import equational_theories.FactsSyntax"
  hPutStrLn handle "import equational_theories.MemoFinOp"
  hPutStrLn handle "import equational_theories.DecideBang"
  hPutStrLn handle ""

emitComment :: Handle -> Magma -> IO ()
emitComment handle magma = do
  hPutStrLn handle "/-!"
  hPutStrLn handle "This file is generated from the following operator table:"
  hPutStrLn handle (show $ Magma.table magma)
  hPutStrLn handle "-/"
  hPutStrLn handle "set_option linter.unusedVariables false"
  hPutStrLn handle ""

emitDefinition :: Handle -> Magma -> IO ()
emitDefinition handle magma = do
  hPutStrLn handle "/-! The magma definition -/"
  hPutStr handle "def «FinitePoly "
  hPutStr handle (show $ Magma.table magma)
  hPutStr handle "» : Magma (Fin "
  hPutStr handle (show $ Magma.size magma)
  hPutStrLn handle ") where"
  hPutStr handle "  op := memoFinOp fun x y => "
  hPutStr handle (show $ Magma.table magma)
  hPutStrLn handle "[x.val]![y.val]!"
  hPutStrLn handle ""

emitFacts :: Handle -> Magma -> [Equation] -> [Equation] -> IO ()
emitFacts handle magma satisfied refuted = do
  hPutStrLn handle "/-! The facts -/"
  hPutStrLn handle "@[equational_result]"
  hPutStr handle "theorem «Facts from FinitePoly "
  hPutStr handle (show $ Magma.table magma)
  hPutStrLn handle "» :"
  hPutStr handle "  ∃ (G : Type) (_ : Magma G), Facts G "
  hPutStr handle (show satisfied)
  hPutStr handle " "
  hPutStr handle (show refuted)
  hPutStrLn handle " :="
  hPutStr handle "    ⟨Fin "
  hPutStr handle (show $ Magma.size magma)
  hPutStr handle ", «FinitePoly "
  hPutStr handle (show $ Magma.table magma)
  hPutStrLn handle "», by decideFin!⟩"

maybeRead :: Read a => String -> Maybe a
maybeRead s = case reads s of
  [(x, "")] -> Just x
  _     -> Nothing
