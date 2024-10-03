module FiniteMagmaTools.Equation (Equation, toInt, fromInt, lowerBound, upperBound) where

import Data.Array

newtype Equation = Equation Int deriving (Eq, Ord, Ix)


lowerBound :: Int
lowerBound = 1 -- NB inclusive

upperBound :: Int
upperBound = 4694 -- NB inclusive

toInt :: Equation -> Int
toInt (Equation x) = x

fromInt :: Int -> Equation
fromInt x
  | x >= lowerBound && x <= upperBound = Equation x
  | otherwise = error ("Equation.fromInt: illegal index " ++ show x)


instance Show Equation where
  show (Equation e) = show e

instance Read Equation where
  readsPrec _ s = [(Equation x, rest) | (x, rest) <- reads s]
