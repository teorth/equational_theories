import Batteries.Data.Array.Basic
import Batteries.Tactic.Lint.Frontend
import Cli.Basic
import Lean.Util.SearchPath
import equational_theories.Closure

open Lean Core Elab Cli

--- Output of the extract_implications executable.
structure Output where
  implications : Array Implication
  nonimplications : Array Implication

--- Output of the extract_implications outcomes subcommand.
structure OutputOutcomes where
  equations : Array String
  outcomes : Array (Array Closure.Outcome)
  deriving Lean.ToJson

def Implication.asJson (v : Implication) : String := s!"\{\"rhs\":\"{v.rhs}\", \"lhs\":\"{v.lhs}\"}"

def Output.asJson (v : Output) : String :=
  s!"\{\"nonimplications\":[{",".intercalate (v.nonimplications.map Implication.asJson).toList}],\"implications\":[{",".intercalate (v.implications.map Implication.asJson).toList}]}"

def generateOutcomes (inp : Cli.Parsed) : IO UInt32 := do
  let some modules := inp.variableArgsAs? ModuleName |
    inp.printHelp
    return 1
  if modules.isEmpty then
    inp.printHelp
    return 2
  searchPathRef.set compile_time_search_path%

  unsafe withImportModules (modules.map ({module := ·})) {} (trustLevel := 1024) fun env =>
    let ctx := {fileName := "", fileMap := default}
    let state := {env}
    Prod.fst <$> (Meta.MetaM.toIO · ctx state) do
      let (equations, outcomes) ← Closure.list_outcomes
      if inp.hasFlag "hist" then
        let mut count : Std.HashMap Closure.Outcome Nat := {}
        for a in outcomes do
          for b in a do
            count := count.insert b (count.getD b 0 + 1)
        IO.print "{"
        for ⟨a, b⟩ in count do
          println! "{a}: {b},"
        IO.println "}"
      else
        IO.println (toJson ({equations, outcomes : OutputOutcomes})).compress
      pure 0

def outcomes : Cmd := `[Cli|
  outcomes VIA generateOutcomes;
  "Output the status of all implications."

  FLAGS:
    hist; "Create a histogram instead of outputting all outcomes"

  ARGS:
    ...files : Array ModuleName; "The files to extract the implications from"
]

def generateOutput (inp : Cli.Parsed) : IO UInt32 := do
  let some modules := inp.variableArgsAs? ModuleName |
    inp.printHelp
    return 1
  if modules.isEmpty then
    inp.printHelp
    return 2
  let include_conj := inp.hasFlag "conjecture"
  let include_impl := inp.hasFlag "closure"
  searchPathRef.set compile_time_search_path%

  unsafe withImportModules (modules.map ({module := ·})) {} (trustLevel := 1024) fun env =>
    let ctx := {fileName := "", fileMap := default}
    let state := {env}
    Prod.fst <$> (Meta.MetaM.toIO · ctx state) do
      let mut rs ← Result.extractEquationalResults
      if !include_conj then
        rs := rs.filter (·.proven)
      let rs' := rs.map (·.variant)
      let rs' := if include_impl then Closure.closure rs' else Closure.toEdges rs'
      if inp.hasFlag "json" then
        let implications := (rs'.filter (·.isTrue)).map (·.get)
        let nonimplications := (rs'.filter (!·.isTrue)).map (·.get)
        IO.println ({implications, nonimplications : Output}).asJson
      else
        for edge in rs' do
          if edge.isTrue then IO.println s!"{edge.lhs} → {edge.rhs}"
          else IO.println s!"¬ ({edge.lhs} → {edge.rhs})"
      pure 0

def extract_implications : Cmd := `[Cli|
  extract_implications VIA generateOutput;
  "Extract the implications shown in the mentioned files."

  FLAGS:
    «conjecture»; "Include conjectures"
    closure; "Compute the transitive closure"
    json; "Output the data as JSON"

  ARGS:
    ...files : Array ModuleName; "The files to extract the implications from"

  SUBCOMMANDS: outcomes
]

def main (args : List String) : IO UInt32 := do
  extract_implications.validate args
