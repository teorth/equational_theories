module ParseMace4.ParseInterps (parseMace4) where

import Text.Regex.Posix
import Data.Char (isDigit)
import Data.List (unfoldr, isPrefixOf)


parseMace4Interp :: String -> Either String [[Int]]
parseMace4Interp s = do
    let s' = filter (/= '\n') s
    -- Use regex to extract the function block
    let ptrn = "function\\(\\+\\(_,_\\),\\s*\\[\\s*(.*?)\\s*\\]\\s*\\)"
    let matches = s' =~ ptrn :: [[String]]
    case matches of
        [] -> Left "Function block not found."
        [[_, numbersStr]] -> do
            -- Extract numbers
            let numbersList = getNumbers numbersStr
            let numbers = map read numbersList :: [Int]
            -- Determine N (size of the square matrix)
            let total_numbers = length numbers
                n = floor (sqrt (fromIntegral total_numbers))
            if n * n == total_numbers
                then Right (chunksOf n numbers)
                else Left "parseMace4Interp: Operator table is not square."
        _ -> Left "parseMace4Interp: Unexpected match."
  where
    chunksOf :: Int -> [a] -> [[a]]
    chunksOf _ [] = []
    chunksOf k xs = take k xs : chunksOf k (drop k xs)
    getNumbers :: String -> [String]
    getNumbers str = case dropWhile (not . isDigit) str of
        "" -> []
        s' -> let (number, rest) = span isDigit s' in number : getNumbers rest

splitByInter :: String -> [String]
splitByInter = foldr f [] . lines
  where
    f line [] = [line]
    f line (x:xs)
      | "inter" `isPrefixOf` line = line : (x:xs)
      | otherwise = (line ++ "\n" ++ x) : xs

parseMace4 :: String -> Either String [[[Int]]]
parseMace4 s =
  let
    ss = drop 1 $ splitByInter s
    ints = map parseMace4Interp ss
  in
    sequence ints
