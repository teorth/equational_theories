module FiniteMagmaTools.Plan where

import FiniteMagmaTools.Equation (Equation)

data PlanEntry
  = PlanEntry
  { peMagma :: String
  , peSatisfies :: [Equation]
  , peRefutes :: [Equation]
  } deriving (Show)

data Plan
  = Plan
  { planTotalCost :: Int
  , planEntries :: [PlanEntry]
  } deriving (Show)

printPlan :: Plan -> IO ()
printPlan plan = do
  putStrLn $
    "Plan " ++ (show.length.planEntries) plan ++ " " ++ show (planTotalCost plan)
  go (planEntries plan)
  where
    go [] = return ()
    go (e:es) = do
      putStrLn $ "Magma " ++ peMagma e
      putStrLn $ "Satisfies " ++ show (peSatisfies e)
      putStrLn $ "Refutes " ++ show (peRefutes e)
      putStrLn ""
      go es
