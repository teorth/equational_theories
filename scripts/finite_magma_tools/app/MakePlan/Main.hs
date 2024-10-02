module Main where

import FiniteMagmaTools.Equation (Equation)
import qualified FiniteMagmaTools.Equation as Equation

import FiniteMagmaTools.Magma (Magma)
import qualified FiniteMagmaTools.Magma as Magma

import FiniteMagmaTools.All4By4Parser
import MakePlan.Plan

import qualified Data.Set as Set
import Data.List (sortOn,intersperse)

import Control.Monad (filterM)
import System.IO
import Data.Array.IO
import System.Environment (getArgs)

displayHelp :: IO ()
displayHelp =
  logger . concat . intersperse "\n" $
    [ "Usage: cabal exec make-plan < in.txt > out.txt"
    , ""
    , "This script generates optimized proof plans from lists of finite magmas"
    , "and their satisfied equations using a cost model. The goal is to reduce"
    , "the number of verifications required by the Lean kernel."
    , "The plan guarantees coverage of all counterexamples from the list, but"
    , "may require fewer verifications or use fewer magmas."
    , ""
    , "The input format is the same as used in All4x4Tables:"
    , "Table [[0,1],[1,0]]  // the operator table"
    , "Proves [1]           // the equation numbers that it satisfies"
    , ""
    , "The output format is "
    , "Magma [[0,1],[1,0]]  // the operator table for G"
    , "Satisfies [1,307]    // eqns whose satisfaction we'll prove in G"
    , "Refutes [2]          // eqns for which we'll find a counterexample in G"
    , ""
    , "By default, all equations are checked. To focus on specific equations,"
    , "adjust `equationsOfInterest` in Main.hs. You can also modify the cost model."
    ]

-------------------------------------------------------------------------------
-- CONFIG SECTION

-- If you want to process implications only between specific equations, write
-- them here.
equationsOfInterest :: [Int]
equationsOfInterest = [Equation.lowerBound..Equation.upperBound]

-- Tune the planner's cost model here.
fitness :: (Equation, Equation) -> MagmaCache -> IO (Maybe Int)
fitness (e1,e2) mc = do
  valid <- disproves (e1,e2) mc
  magmaUsed <- readArray (mcUsed mc) 0
  pUsed <- readArray (mcSatisfiesPlanned mc) e1
  nUsed <- readArray (mcRefutesPlanned mc) e2
  let l = Magma.size (mcMagma mc)
  let cu = if magmaUsed then 0 else l
    -- introducing new magmas is penalized proportionally to their size
  let c1 = if pUsed then 0 else l*l
    -- checking that all elements satisfy a given equation is O(n^2) in
    -- the number of elements.
  let c2 = if nUsed then 0 else 1
    -- checking a refutation is O(1), assuming that eventually we will
    -- just precompute the counterexamples for Lean.
  let result = if valid then Just (0 - cu - c1 - c2) else Nothing
  return result

-------------------------------------------------------------------------------

disproves :: (Equation, Equation) -> MagmaCache -> IO Bool
disproves (p,n) mc = do
  psat <- readArray (mcSatisfies mc) p
  nsat <- readArray (mcSatisfies mc) n
  return (psat && not nsat)

logger :: String -> IO ()
logger = hPutStrLn stderr

data MagmaCache
  = MagmaCache
  { mcMagma :: Magma
  , mcUsed :: IOArray Int Bool -- NB profiler says Int faster than ()
  , mcSatisfies :: IOArray Equation Bool
  , mcSatisfiesPlanned :: IOArray Equation Bool
  , mcRefutesPlanned :: IOArray Equation Bool
  }

loggerTI :: (Show ix, Ix ix) => IOArray ix Bool -> IO ()
loggerTI arr = do
    bounds <- getBounds arr
    indices <- filterM (\ix -> readArray arr ix) (range bounds)
    logger (show indices)


recordToCache :: Magma.Record -> IO MagmaCache
recordToCache mr = do
  let lb = Equation.fromInt (Equation.lowerBound)
  let ub = Equation.fromInt (Equation.upperBound)
  mcu <- newArray (0,0) False :: IO (IOArray Int Bool)
  mcs <- newArray (lb,ub) False :: IO (IOArray Equation Bool)
  mapM_ (\x -> writeArray mcs x True) (Magma.satisfies mr)
  mcsp <- newArray (lb,ub) False :: IO (IOArray Equation Bool)
  mcrp <- newArray (lb,ub) False :: IO (IOArray Equation Bool)
  return $ MagmaCache (Magma.fromRecord mr) mcu mcs mcsp mcrp

planEntryToCache :: PlanEntry -> IO MagmaCache
planEntryToCache pe = do
  let lb = Equation.fromInt (Equation.lowerBound)
  let ub = Equation.fromInt (Equation.upperBound)
  mcu <- newArray (0,0) False :: IO (IOArray Int Bool)
  mcs <- newArray (lb,ub) False :: IO (IOArray Equation Bool)
  mapM_ (\x -> writeArray mcs x True) (peSatisfies pe)
  mcsp <- newArray (lb,ub) False :: IO (IOArray Equation Bool)
  mapM_ (\x -> writeArray mcsp x True) (peSatisfies pe)
  mcrp <- newArray (lb,ub) False :: IO (IOArray Equation Bool)
  mapM_ (\x -> writeArray mcrp x True) (peSatisfies pe)
  return $ MagmaCache (Magma.fromTable . read . peMagma $ pe) mcu mcs mcsp mcrp

updateCache :: (Equation, Equation) -> MagmaCache -> IO (Maybe Int)
updateCache (p,n) cache = do
  cost <- fitness (p,n) cache
  case cost of
    Nothing ->
      return Nothing
    Just c -> do
      writeArray (mcUsed cache) 0 True
      writeArray (mcSatisfiesPlanned cache) p True
      writeArray (mcRefutesPlanned cache) n True
      return (Just (0 - c))

withMaxBy :: (Ord b) => (a -> IO b) -> (a -> IO (Maybe Int)) -> [a] -> IO (Maybe Int)
withMaxBy f act [] = return Nothing
withMaxBy f act (x:xs) = do
  fx <- f x
  go x fx xs where
  go x fx [] = act x
  go x fx (y:ys) = do
    fy <- f y
    if fy > fx then go y fy ys
    else go x fx ys

filterIndices :: (Ix a) => [a] -> IOArray a Bool -> IO [a]
filterIndices indices arr = filterM (\i -> readArray arr i) indices

data MakePlanState
  = MakePlanState
  { mpsTotalCost :: Int
  , mpsTotalCovered :: Int
  , mpsCache :: [MagmaCache]
  }

makePlan :: [Equation] -> [Magma.Record] -> IO MakePlanState
makePlan equations records = do
  logger $ "makePlan: caching " ++ show (length records) ++ " magmas."
  icache <- mapM recordToCache records
  let istate = MakePlanState 0 0 icache
  logger $ "makePlan: starting on " ++ show (length equations) ++ " equations."
  go equations equations istate
  where
    go [] _ acc = do
      logger $ "makePlan: finished with cost " ++ show (mpsTotalCost acc) ++ "."
      return acc
    go (p:pos) [] acc = do
      logger $ "makePlan: " ++ show (length pos) ++ " equations left."
      logger $
        "makePlan: cost so far is " ++ show (mpsTotalCost acc) ++
        ", covering " ++ show (mpsTotalCovered acc) ++
        " implications."
      go pos equations acc
    go (p:pos) (n:neg) acc = do
      let pn = (p,n)
      c <- withMaxBy (fitness pn) (updateCache pn) (mpsCache acc)
      case c of
        Nothing -> go (p:pos) neg acc
        Just c' ->
          let
            acc' = MakePlanState
              (mpsTotalCost acc + c')
              (mpsTotalCovered acc + 1)
              (mpsCache acc)
          in
            go (p:pos) neg acc'

finalizePlan :: [Equation] -> MakePlanState -> IO Plan
finalizePlan equations mps = do
  let cost = mpsTotalCost mps
  let covered = mpsTotalCovered mps
  entries <- go (mpsCache mps) []
  logger $
    "finalizePlan: " ++ show (length entries) ++
    " magmas, covered " ++ show covered ++
    " equations at cost " ++ show cost
  return (Plan cost entries)
  where
    go [] acc = return (reverse acc)
    go (c:cs) acc = do
      used <- readArray (mcUsed c) 0
      if not used then go cs acc else do
        let name = Magma.name (mcMagma c)
        pes <- filterIndices equations (mcSatisfiesPlanned c)
        per <- filterIndices equations (mcRefutesPlanned c)
        let pe = PlanEntry name pes per
        go cs (pe:acc)


main :: IO ()
main = do
  args <- getArgs
  if "--help" `elem` args || "-h" `elem` args
    then displayHelp
    else do
      input <- getContents
      case parseRecords input of
        Left err -> do
          logger "Parse Error"
          logger "-----------"
          logger err
        Right records -> do
          let eqns = map Equation.fromInt equationsOfInterest
          p1 <- makePlan eqns records
          p2 <- finalizePlan eqns p1
          printPlan p2
