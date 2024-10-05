module FiniteMagmaTools.Evaluator
  ( Program
  , Relation (Relation), equation, lhs, rhs
  , variables
  , parseRelations
  , runProgram, checkRelation
  , satisfied
  ) where

import FiniteMagmaTools.Equation (Equation)
import qualified FiniteMagmaTools.Equation as Equation

import FiniteMagmaTools.Magma (Magma)
import qualified FiniteMagmaTools.Magma as Magma

import Data.Char (isAlphaNum, isSpace, isAscii)
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set

-- a type for RPN programs
newtype Program
  = Program [String] 
  deriving (Show, Eq)

data Relation
  = Relation
  { equation :: Equation
  , lhs :: Program
  , rhs :: Program
  } deriving (Show)

-- All equations that hold in the magma with given optable.
satisfied :: [Relation] -> Magma -> Set Equation
satisfied relations magma =
  Set.fromList $
  map equation $
  filter (checkRelation (Magma.table magma)) relations

variables :: Relation -> [String]
variables rel =
  let
    vars (Program p) = filter isOperand p
  in
    nub $ vars (lhs rel) `union` vars (rhs rel)

cartesianProduct :: [[a]] -> [[a]]
cartesianProduct [] = [[]]
cartesianProduct (xs:xss) = [ x:ys | x <- xs, ys <- cartesianProduct xss ]

-- Check if a given equation holds in magma with given optable
checkRelation :: [[Int]] -> Relation -> Bool
checkRelation op rel =
  let
    bound = length op
    vals x = [(x,n) | n <- [0..bound-1]]
    assignments = cartesianProduct (map vals (variables rel))
    counterexamples =
      [ xs | xs <- assignments
      , let lres = runProgram (lhs rel) op xs
      , let rres = runProgram (rhs rel) op xs
      , lres /= rres
      ]
  in
    counterexamples == []

runProgram :: Program -> [[Int]] -> [(String,Int)] -> Int
runProgram (Program p) op vars = go [] p where
  go [] [] = 0
  go (v:vs) [] = v
  go (v1:v2:vs) (p:ps)
    | isOperator p =
        let r = (op !! v2) !! v1 in go (r:vs) ps
    | isOperand p =
        case lookup p vars of
          Nothing ->
            error $ "runProgram: " ++ show (vars,v1:v2:vs,p:ps)
          Just v -> go (v:v1:v2:vs) ps
    | otherwise =
        error $ "runProgram: " ++ show (vars,v1:v2:vs,p:ps)
  go vs (p:ps)
    | isOperand p =
        case lookup p vars of
          Nothing ->
            error $ "runProgram: " ++ (show (vars,vs,p:ps))
          Just v -> go (v:vs) ps
    | otherwise =
        error $ "runProgram: " ++ show (vars,vs,p:ps)

-- Convert an equation database (in the equations.txt format)
-- into a list of checkable relations.
parseRelations :: String -> [Relation]
parseRelations input =
  let
    lineNumbers =
      map Equation.fromInt [Equation.lowerBound..Equation.upperBound]
    linput = zip lineNumbers (lines input)
    getLHS = shuntingYard . takeWhile (/= '=')
    getRHS = shuntingYard . drop 1 . dropWhile (/= '=')
  in
    [Relation e (getLHS x) (getRHS x) | (e,x) <- linput]

-- Convert infix string to RPN program using the shunting yard algorithm
shuntingYard :: String -> Program
shuntingYard expr =
  Program (shuntingYard' (tokenize $ replaceOpSymbol expr) [] [])

shuntingYard' :: [String] -> [String] -> [String] -> [String]
shuntingYard' [] [] output = reverse output
shuntingYard' [] (op:ops) output = shuntingYard' [] ops (op:output)
shuntingYard' (t:ts) stack output
  | isOperand t = shuntingYard' ts stack (t:output)
  | isOperator t = shuntingYard' ts (pushOperator t stack) output
  | t == "(" = shuntingYard' ts (t:stack) output
  | t == ")" = shuntingYard' ts newStack newOutput
  | otherwise = error $ "shuntingYard: " ++ show (t:ts,stack,output)
    where
        (newStack, newOutput) = popUntilLeftParen stack output

-- we support both +/*/◇ and composition notation for the magma op, but
-- the latter is processed in replaceOpSymbol
isOperator :: String -> Bool
isOperator "+" = True
isOperator "*" = True
isOperator _ = False

isOperand :: String -> Bool
isOperand s = all isAlphaNum s

isSymbol :: String -> Bool
isSymbol c = c `elem` (map singleton "+*()")

pushOperator :: String -> [String] -> [String]
pushOperator op (s:ss)
    | isOperator s = op:s:ss
pushOperator op stack = op:stack

popUntilLeftParen :: [String] -> [String] -> ([String], [String])
popUntilLeftParen [] _ = error "popUntilLeftParen: Mismatched parentheses"
popUntilLeftParen (s:ss) output
    | s == "(" = (ss, output)
    | otherwise = popUntilLeftParen ss (s:output)

tokenize :: String -> [String]
tokenize [] = []
tokenize (c:cs)
    | isAlphaNum c =
        let
          (token, rest) = span isAlphaNum (c:cs)
        in
          token : tokenize rest
    | isSymbol [c] = [c] : tokenize cs
    | isSpace c = tokenize cs
    | otherwise = error ("tokenize: bad character " ++ [c])

-- Replace the composition symbol with '+' - that symbol is two codepoints
-- which causes complications.
replaceOpSymbol :: String -> String
replaceOpSymbol [] = []
replaceOpSymbol ('◇':xs) = '+':replaceOpSymbol xs
replaceOpSymbol ('\9702':'\65038':xs) = '+':replaceOpSymbol xs
replaceOpSymbol (x:xs) = x:replaceOpSymbol xs
