import Batteries.Data.Array.Basic
import Batteries.Tactic.Lint.Frontend
import Cli.Basic
import Lean.Util.SearchPath
import equational_theories.Closure

open Lean Core Elab Cli

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
      let mut rs' := if include_impl then Closure.closure rs' else Closure.toEdges rs'
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

  ARGS:
    ...files : Array ModuleName; "The files to extract the implications from"
]

def main (args : List String) : IO UInt32 := do
  extract_implications.validate args
