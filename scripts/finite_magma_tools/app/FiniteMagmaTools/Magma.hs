module FiniteMagmaTools.Magma
  ( Magma, fromTable, name, size, table
  , Record (Record), fromRecord, satisfies
  ) where

import FiniteMagmaTools.Equation (Equation)
import Data.Set (Set)

data Magma
  = Magma
  { name :: String
  , size :: Int
  , table :: [[Int]]
  } deriving (Show)

instance Eq Magma where
  m1 == m2 = name m1 == name m2

instance Ord Magma where
  m1 <= m2 = name m1 <= name m2

fromTable :: [[Int]] -> Magma
fromTable table =
  let
    size = length table
    validEntry x = 0 <= x && x < size
    validRow xs = length xs == size && all validEntry xs
  in
    if size > 0 && all validRow table
      then Magma (show table) size table
      else error $
        "Magma.fromTable: Multiplication table is invalid " ++ show table

data Record
  = Record
  { fromRecord :: Magma
  , satisfies :: Set Equation
  } deriving (Show)
