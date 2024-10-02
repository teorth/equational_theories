module MakePlan.PlanParser (parsePlan) where

import MakePlan.Plan
import FiniteMagmaTools.Equation (Equation)
import qualified FiniteMagmaTools.Equation as Equation

import Data.List (isPrefixOf)

data ParserState
  = ExpectPlan
  | ExpectMagma
  | ExpectSatisfies String
  | ExpectRefutes String [Int]
  deriving (Show)

parsePlan :: String -> Either String Plan
parsePlan content =
  case parseLines (zip [1..] (lines content)) of
    Left err -> Left err
    Right (planLine, entries) ->
      let
        cost = last (words planLine)
      in
        case maybeRead cost :: Maybe Int of
          Nothing ->
            Left "PlanParser: Invalid Plan line"
          Just cost' ->
            Right (Plan cost' entries)

parseLines :: [(Int, String)] -> Either String (String, [PlanEntry])
parseLines lines = parseLines' lines ExpectPlan [] ""

parseLines' :: [(Int, String)] -> ParserState -> [PlanEntry] -> String
      -> Either String (String, [PlanEntry])
parseLines' [] state acc planLine =
  case state of
    ExpectPlan ->
      Left "PlanParser: Unexpected EOF: expected 'Plan' line."
    ExpectMagma ->
      Right (planLine, reverse acc)
    ExpectSatisfies _ ->
      Left "PlanParser: Unexpected EOF: expected 'Satisfies' line."
    ExpectRefutes _ _ ->
      Left "PlanParser: Unexpected EOF: expected 'Refutes' line."
parseLines' ((lineNum, line):rest) state acc planLine =
  case state of
    ExpectPlan ->
      if "Plan " `isPrefixOf` line
        then
          let
            planLine = drop (length "Plan ") line
          in
            parseLines' rest ExpectMagma acc planLine
      else
        Left $ "PlanParser: Expected 'Plan' on line " ++ show lineNum ++ "."
    ExpectMagma ->
      if "Magma " `isPrefixOf` line
      then
        let
          xs = drop (length "Magma ") line
        in
          parseLines' rest (ExpectSatisfies xs) acc planLine
      else
        if any (`isPrefixOf` line) ["Satisfies ", "Refutes ", "Plan "]
          then Left $ "PlanParser: Unexpected '" ++ takeWhile (/=' ') line ++
                      "' on line " ++ show lineNum ++ ", expected 'Magma'."
          else parseLines' rest state acc planLine
    ExpectSatisfies xs ->
      if "Satisfies " `isPrefixOf` line
        then
          let
            ysStr = drop (length "Satisfies ") line
          in case parseListOfInts ysStr of
            Just ys -> parseLines' rest (ExpectRefutes xs ys) acc planLine
            Nothing -> Left $ "Invalid equations on line " ++
                              show lineNum ++ " in 'Satisfies'."
        else
          if any (`isPrefixOf` line) ["Magma ", "Refutes ", "Plan "]
            then Left $ "PlanParser: Unexpected '" ++ takeWhile (/=' ') line ++
                        "' on line " ++ show lineNum ++ ", expected 'Satisfies'."
            else parseLines' rest state acc planLine  -- Ignore other lines
    ExpectRefutes xs ys ->
      if "Refutes " `isPrefixOf` line
        then
          let
            zsStr = drop (length "Refutes ") line
          in case parseListOfInts zsStr of
            Just zs ->
              let
                entry = PlanEntry xs (map Equation.fromInt ys) (map Equation.fromInt zs)
              in
                parseLines' rest ExpectMagma (entry:acc) planLine
            Nothing ->
              Left $ "PlanParser: Invalid equations on line " ++
                     show lineNum ++ " in 'Refutes'."
        else if any (`isPrefixOf` line) ["Magma ", "Satisfies ", "Plan "]
           then Left $ "PlanParser: Unexpected '" ++ takeWhile (/=' ') line ++
                       "' on line " ++ show lineNum ++ ", expected 'Refutes'."
           else parseLines' rest state acc planLine

parseListOfInts :: String -> Maybe [Int]
parseListOfInts s = maybeRead s

maybeRead :: Read a => String -> Maybe a
maybeRead s = case reads s of
  [(x, "")] -> Just x
  _     -> Nothing
