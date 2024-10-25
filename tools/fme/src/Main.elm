port module Main exposing (..)

import Browser
import Browser.Navigation
import Html exposing (Html, div, text, input, button, textarea, p, a, h1, h3, span, ul, li, pre, label)
import Html.Attributes exposing (placeholder, value, id, class, rows)
import Html.Events exposing (onClick, onInput)
import Url exposing (Url, percentEncode, percentDecode)
import String exposing (split, startsWith, dropLeft)
import Maybe exposing (withDefault)
import Set

import Parsing exposing (parseInput)
import Html.Attributes exposing (href)
import Html exposing (Attribute)
import Debug exposing (toString)


{- MODEL -}

type alias ModelInfoSuccess =
  { satisfied : List (Int, String)
  , refuted : List (Int, String)
  , novel : List (Int, Int)
  }

type ModelInfo
  = ModelInfoNone
  | ModelInfoSpinner
  | ModelInfoError String
  | ModelInfo ModelInfoSuccess

type alias Model =
  { key : Browser.Navigation.Key
  , currentUrl : Url
  , optable : String
  , matcherInput : String
  , modelInfo : ModelInfo
  , version : String
  }

type Msg
  = UrlChanged Url
  | UrlRequested Browser.UrlRequest
  | SetUrl
  | OptableChanged String
  | MatcherChanged String
  | ClickProcessBtn
  | ExploreEquation Int
  | ListenMagma ModelInfo


{- UPDATE -}

port checkMagma : List (List Int) -> Cmd msg
port openInNewTab : String -> Cmd msg
port checkMagmaListener : (ModelInfoSuccess -> msg) -> Sub msg

update : Msg -> Model -> ( Model, Cmd Msg )
update msg model =
  case msg of
    UrlChanged url ->
      let
        maybeMagma = parseQuery url
        magma = Maybe.withDefault "" maybeMagma
      in
        ({ model | optable = magma, currentUrl = url }, Cmd.none)

    UrlRequested urlRequest ->
      case urlRequest of
        Browser.Internal url ->
          (model, Browser.Navigation.pushUrl model.key (Url.toString url))
        Browser.External href ->
          (model, Browser.Navigation.load href)

    OptableChanged newInput ->
      ({model | optable = newInput}, Cmd.none)

    MatcherChanged newInput ->
      ({model | matcherInput = newInput}, Cmd.none)

    SetUrl ->
      let
        encodedInput = percentEncode model.optable
        currentPath = model.currentUrl.path
        newUrl = currentPath ++ "?magma=" ++ encodedInput
      in
        (model, Browser.Navigation.pushUrl model.key newUrl)

    ClickProcessBtn ->
      case parseInput model.optable of
        Err err ->
          let
            newModel =
              {model | modelInfo = ModelInfoError err}
          in
            (newModel, Cmd.none)
        Ok magma ->
          let
            newModel = {model | modelInfo = ModelInfoSpinner}
          in
            (newModel, checkMagma magma)

    ExploreEquation num ->
      let
        base =
          "https://teorth.github.io/equational_theories/implications/?"
        url =
          base ++ String.fromInt num
      in
        (model, openInNewTab url)

    ListenMagma mi ->
      let
        newModel =
          {model | modelInfo = mi}
      in
        update SetUrl newModel

{- VIEWS -}

viewLeftPanel : Model -> Html Msg
viewLeftPanel model =
  div [class "panel left-panel"]
   [ h3 [] [text "Operation table:"]
   , textarea
       [ id "textbox"
       , class "textarea"
       , rows 14
       , onInput OptableChanged
       , placeholder ""
       ] [text model.optable]
   , button [id "process-button", onClick ClickProcessBtn] [ text "Process" ]
   ]


viewSpinner : Html msg
viewSpinner =
  div [class "spinner-container"] [ div [class "spinner"] []]

viewEquationTag : (Int, String) -> Html Msg
viewEquationTag tag =
  case tag of
    (num, info) ->
      li [onClick (ExploreEquation num)]
        [text (String.fromInt num), text " - ", text info]

viewEquationTags : List (Int, String) -> Html Msg
viewEquationTags tags =
  div [ class "scrollable-container" ]
    [ul [] (List.map viewEquationTag tags)]

graphitiEq : (Int, String) -> String
graphitiEq (a, _) = String.fromInt a ++ ","

graphitiLink : List (Int, String) -> String
graphitiLink tags = "/equational_theories/graphiti/?render=true&limit_equations=" ++
  (String.join "+" (List.map graphitiEq tags))

matchInput : String -> (Int, String) -> Bool
matchInput matcher tag =
  case tag of
    (num, eqn) ->
      String.startsWith matcher (String.fromInt num)               ||
      String.contains matcher (String.filter (\x -> x /= ' ') eqn)

viewMatchingFilter : String -> Html Msg
viewMatchingFilter matcher =
  div [class "matcher-container"]
    [ label [] [ text "Filter: " ]
    , input [ placeholder "number or expression", value matcher, onInput MatcherChanged ] []
    ]

viewExportNovel : String -> List (Int, String) -> List (Int, Int) -> Html Msg
viewExportNovel table satisfies novel =
  case novel of
    [] ->
      div []
        [text "All implications refuted by this magma are already known."]
    _ ->
      let
        count = String.fromInt (List.length novel)
        showInts xs =
          xs |>
          Set.fromList |>
          Set.toList |>
          List.map String.fromInt |>
          String.join "," |>
          (\x -> "[" ++ x ++ "]")
        showRow xs =
          xs |>
          List.map String.fromInt |>
          String.join "," |>
          (\x -> "[" ++ x ++ "]")
        showMagma xs =
          xs |>
          List.map showRow |>
          String.join "," |>
          (\x -> "[" ++ x ++ "]")
      in
        case parseInput table of
          Err err -> div [] []
          Ok magma ->
            let
              tableString = magma |> showMagma
              magmaLine =
                tableString |>
                (\m -> "Magma " ++ m ++ "\n")
              sat =
                novel |>
                List.map (\(x,y) -> x) |>
                showInts |>
                (\m -> "Satisfies " ++ m ++ "\n")
              ref =
                novel |>
                List.map (\(x,y) -> y) |>
                showInts |>
                (\m -> "Refutes " ++ m ++ "\n")
              tableLine =
                tableString |>
                (\m -> "Table " ++ m ++ "\n")
              prov =
                satisfies |>
                List.map (\(x,y) -> x) |>
                showInts |>
                (\m -> "Proves " ++ m ++ "\n")
            in
              div []
                [ h3 [] [text "Export"]
                , text "Congratulations! "
                , text ("This magma refutes " ++ count ++ " previously unknown potential implications!")
                , text " Create a PR. Add the following code to plan.txt in `All4x4Tables/data`:"
                , div [class "code-container"] [pre [] [text (magmaLine ++ sat ++ ref)]]
                , text "Then add the following to extra.txt in `All4x4Tables/data`:"
                , div [class "code-container"] [pre [] [text (tableLine ++ prov)]]
                , text "Finally, re-run `python3 equational_theories/Generated/FinSearch/src/generate_lean.py`!"
                ]

viewModelInfo : String -> String -> ModelInfoSuccess -> Html Msg
viewModelInfo table matcher mi =
  let
    tmatcher =
      matcher |>
      String.filter (\x -> x /= ' ') |>
      String.replace "+" "◇" |>
      String.replace "*" "◇"
    matching xs =
      if tmatcher == ""
        then xs
        else List.filter (matchInput tmatcher) xs
  in
    div []
      [ h3 [] [a [ href (graphitiLink (matching mi.satisfied))] [ text "Satisfies"], text ": "]
      , viewEquationTags (matching mi.satisfied)
      , h3 [] [text "Refutes: "]
      , viewEquationTags (matching mi.refuted)
      , viewMatchingFilter matcher
      , viewExportNovel table mi.satisfied mi.novel
      ]

viewRightPanel : Model -> Html Msg
viewRightPanel model =
  case model.modelInfo of
    ModelInfoNone ->
      div [class "panel right-panel"]
        [ h3 [] [text "Help"]
        , p [] [text "Type in an operator table, then press Process to begin."]
        , p [] [text "Supported formats include:"]
        , pre [] [text "0 1\n1 0"]
        , pre [] [text "[[0,1],[1,0]]"]
        , pre [] [text "{{0, 1}, {1, 0}}"]
        ]
    ModelInfoSpinner ->
      div [class "panel right-panel"] [viewSpinner]
    ModelInfoError err ->
      div [class "panel right-panel"]
        [ h3 [] [text "Error"]
        , p [] [text "I have encountered an error while parsing your operator table. ", text err]
        ]
    ModelInfo mi ->
      div [class "panel right-panel"] [viewModelInfo model.optable model.matcherInput mi]


view : Model -> Browser.Document Msg
view model =
  Browser.Document "Finite Magma Explorer"
    [ h1 [id "title"] [text "Finite Magma Explorer"]
    , div [class "container"]
      [ viewLeftPanel model
      , viewRightPanel model
      ]
    , div [class "copyright"]
      [text ("© 2024 The Equational Theories Project / data: " ++ String.left 7 model.version)]
    ]


{- MAIN APPLICATION -}

parseQuery : Url -> Maybe String
parseQuery url =
  case url.query of
    Just queryString ->
      let
        params = split "&" queryString
        magmaParam = List.filter (startsWith "magma=") params
      in
      case magmaParam of
        [ magma ] ->
          percentDecode (dropLeft 6 magma)
        _ -> Nothing

    Nothing ->
      Nothing

subscriptions : Model -> Sub Msg
subscriptions _ =
    checkMagmaListener (\x -> x |> ModelInfo |> ListenMagma)

init : String -> Url -> Browser.Navigation.Key -> ( Model, Cmd Msg )
init version url key =
  let
    maybeMagma = parseQuery url
    magma = Maybe.withDefault "" maybeMagma
  in
    ( { key = key
      , currentUrl = url
      , optable = magma
      , matcherInput = ""
      , modelInfo = ModelInfoNone
      , version = version}
    , Cmd.none
    )

main =
  Browser.application
    { init = init
    , update = update
    , view = view
    , subscriptions = subscriptions
    , onUrlChange = UrlChanged
    , onUrlRequest = UrlRequested
    }
