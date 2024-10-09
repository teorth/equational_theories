module Parsing exposing (parseInput)

import Json.Decode as Decode exposing (Decoder)
import String exposing (split, trim, lines, replace)
import List exposing (map)

hasBrackets : String -> Bool
hasBrackets inputStr =
  String.contains "[" inputStr && String.contains "]" inputStr

convertToJsonArray : String -> String
convertToJsonArray inputStr =
  let
    cleanRow row =
      row
        |> trim
        |> String.split " "
        |> List.filter (\x -> x /= "")
        |> String.join ","
    rows = lines inputStr
    jsonRows = List.map (\row -> "[" ++ cleanRow row ++ "]") rows
  in
    "[" ++ String.join "," jsonRows ++ "]"


listOfListsDecoder : Decoder (List (List Int))
listOfListsDecoder =
  Decode.list (Decode.list Decode.int)

normalizeSymbols : String -> String
normalizeSymbols input =
  input
    |> replace "{" "["
    |> replace "}" "]"
    |> replace ";" ","

checkValidMagma : List (List Int) -> Result String ()
checkValidMagma rows =
  case rows of
    [] -> Err "The empty magma is not supported."
    _ ->
      let
        correctRow : List Int -> Result String ()
        correctRow r =
          if List.length r /= List.length rows
            then Err "The operator table must be square."
            else 
              case List.filter (\e -> e < 0 || e >= List.length rows) r of
                [] -> Ok ()
                (e :: _) -> Err ("Invalid entry: " ++ String.fromInt e ++ ".")
        correctMagma : List (List Int) -> Result String ()
        correctMagma row = case row of
          [] -> Ok ()
          (r :: rs) ->
            case correctRow r of
              Err x -> Err x
              Ok () -> correctMagma rs
      in
        correctMagma rows

parseInput : String -> Result String (List (List Int))
parseInput inputStr =
  let
    trimmedInput = inputStr |> normalizeSymbols |> trim
    jsonInput =
      if hasBrackets trimmedInput then
        trimmedInput
      else
        convertToJsonArray trimmedInput
  in
    case Decode.decodeString listOfListsDecoder jsonInput of
      Ok result ->
        case checkValidMagma result of
          Err err -> Err err
          Ok () -> Ok result
      Err error ->
        Err (Decode.errorToString error)
