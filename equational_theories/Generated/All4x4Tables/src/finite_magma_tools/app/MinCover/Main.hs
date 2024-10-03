{-# LANGUAGE ScopedTypeVariables #-}

module Main where
        
import Data.SBV
import qualified Data.Set as Set
import Data.List (intersperse)

import System.IO
import System.Environment (getArgs)

import qualified FiniteMagmaTools.Magma as Magma
import qualified FiniteMagmaTools.Equation as Equation
import FiniteMagmaTools.All4By4Parser
import qualified Data.Foldable as F

import FiniteMagmaTools.Plan
import FiniteMagmaTools.PlanParser

displayHelp :: IO ()
displayHelp =
  logger . concat . intersperse "\n" $
    [ "Usage: cabal exec min-cover < in.txt > out.txt"
    , ""
    , "This script finds a minimal subset of the given list of finite magmas"
    , "and equations they satisfy which still provides counterexamples to the"
    , "same set of potential implications."
    , "The returned plan is guaranteed to cover all the same counterexamples as"
    , "the original list, but may have fewer magmas."
    , ""
    , "Optimization is done using an SMT solver."
    , "This process is slow for large equation sets or many magmas, so adjust"
    , "`equationsOfInterest` in the config section of Main.hs before running."
    , ""
    , "Input format: All4x4Tables or make-plan outputs."
    ]

-------------------------------------------------------------------------------
-- CONFIG SECTION

-- The equations for which you want a minimum cover. Note that using too many
-- equations will slow down the solver substantially -- you cannot run this
-- with the full set of equations at the moment (but you might after pruning)
equationsOfInterest :: [Equation.Equation]
equationsOfInterest =
  map Equation.fromInt [1..10]

-------------------------------------------------------------------------------

logger :: String -> IO ()
logger = hPutStrLn stderr

symbolicInSet :: Traversable t => SBV Integer -> t Integer -> SBool
symbolicInSet x set = sAny (\elem -> x .== literal elem) (F.toList set)

oneWhen :: SBool -> SInteger
oneWhen b = ite b 1 0

satMinimumCoverPlan :: [PlanEntry] -> IO ()
satMinimumCoverPlan plan = do
  let n = length plan
  logger $ "satMinimumCoverPlan: reaching out to solver..."
  result <- optimize Lexicographic $ do
    -- symbols for selecting sets
    xs <- sBools ["x" ++ show i | i <- [1..n]]

    -- ensure that every pair is covered by some selected set
    let
      coverageConstraints = 
        [ do
            let sElemList j = map (fromIntegral . Equation.toInt) (peSatisfies (plan !! j))
            let rElemList j = map (fromIntegral . Equation.toInt) (peRefutes (plan !! j))
            constrain $
              flip sAll (sElemList i) (\s ->
                flip sAll (rElemList i) (\r ->
                  flip sAny [0..n-1] (\j -> 
                     xs !! j .&&
                     symbolicInSet (literal s) (sElemList j) .&&
                     symbolicInSet (literal r) (rElemList j)
                  )
                ) 
              ) 
        | i <- [0..n-1]
        ]
    sequence_ coverageConstraints
    minimize "total_sets" $ sum (map oneWhen xs)
  logger $ "satMinimumCoverPlan: inspecting returned model..."
  case result of
    LexicographicResult model -> do
      let xsBools = map (\i -> getModelValue ("x" ++ show i) model) [1..n]
      let boolsList = map (\(Just b) -> b) xsBools
      let numSets = length (filter id boolsList)
      let chosenPlan = [e | (x,e) <- zip boolsList plan, x]
      printPlan (Plan (-1) chosenPlan)
    _ -> do
      logger "SMT error"
      logger (show result)


recordToPlan :: Magma.Record -> PlanEntry
recordToPlan record =
  let
    sats = Set.toList (Magma.satisfies record)
  in
    PlanEntry
      (Magma.name $ Magma.fromRecord record)
      [e | e <- equationsOfInterest, e `elem` sats]
      [e | e <- equationsOfInterest, not (e `elem` sats)]

recordsToPlan :: [Magma.Record] -> [PlanEntry]
recordsToPlan records = map recordToPlan records

main :: IO ()
main = do
  args <- getArgs
  if "--help" `elem` args || "-h" `elem` args
    then displayHelp
    else do
      input <- getContents
      case parsePlan input of
        Left err1 -> do
          case parseRecords input of
            Left err2 -> do
              logger "Parse Error"
              logger "-----------"
              logger err1
              logger err2
            Right records ->
              satMinimumCoverPlan (recordsToPlan records)
        Right plan ->
          satMinimumCoverPlan (planEntries plan)
