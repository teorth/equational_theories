module FiniteMagmaTools.All4By4Parser (parseRecords) where

{-
  This is a parser for the file format used by the tools in
  `/equational_theories/Generated/All4x4Tables/`. It returns a list of
  Magma.Record data given such a file.
-}

import FiniteMagmaTools.Equation (Equation)
import qualified FiniteMagmaTools.Equation as Equation

import FiniteMagmaTools.Magma (Magma)
import qualified FiniteMagmaTools.Magma as Magma

import Data.List (isPrefixOf)
import qualified Data.Set as Set

data ParserState
  = ExpectTable
  | ExpectProves Magma
  deriving (Show)

parseRecords :: String -> Either String [Magma.Record]
parseRecords input = parseLines (zip [1..] $ lines input)

parseLines :: [(Int, String)] -> Either String [Magma.Record]
parseLines lines = parseLines' lines ExpectTable []

parseLines' :: [(Int, String)] -> ParserState -> [Magma.Record] ->
               Either String [Magma.Record]
parseLines' [] state acc =
  case state of
    ExpectTable ->
      Right (reverse acc)
    _ ->
      Left "All4By4Parser: Unexpected EOF: expected 'Proves' line."
parseLines' ((lineNum, line):rest) state acc =
  case state of
    ExpectTable ->
      if "Table " `isPrefixOf` line
      then
        let
          xs = drop (length "Table ") line
          xs' = filter (flip elem "0123456789,[]") xs
          rs = maybeRead xs' :: Maybe [[Int]]
        in
          case rs of
            Nothing ->
              Left $ "All4By4Parser: Invalid multiplication table on line " ++ show lineNum
            Just table ->
              parseLines' rest (ExpectProves $ Magma.fromTable table) acc
      else
        if "Proves " `isPrefixOf` line
          then Left $ "All4By4Parser: Unexpected 'Proves'" ++
                      " on line " ++ show lineNum ++ ", expected 'Table'."
          else parseLines' rest state acc
    ExpectProves magma ->
      if "Proves " `isPrefixOf` line
        then
          let
            zsStr = drop (length "Proves ") line
          in case parseListOfInts zsStr of
            Just zs ->
              let
                proves = map Equation.fromInt zs
                record = Magma.Record magma (Set.fromList proves)
              in
                parseLines' rest ExpectTable (record:acc)
            Nothing ->
              Left $ "All4By4Parser: Invalid equations on line " ++
                     show lineNum ++ " in 'Proves'."
        else if "Table " `isPrefixOf` line
           then Left $ "All4By4Parser: Unexpected 'Table'" ++
                       "' on line " ++ show lineNum ++ ", expected 'Proves'."
           else parseLines' rest state acc

parseListOfInts :: String -> Maybe [Int]
parseListOfInts s = maybeRead s

maybeRead :: Read a => String -> Maybe a
maybeRead s = case reads s of
  [(x, "")] -> Just x
  _     -> Nothing
