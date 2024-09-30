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
  unconditionals : Array String
deriving Lean.ToJson, Lean.FromJson

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
      let rs ← Closure.collectClosure
      for ⟨⟨lhs, rhs⟩, outcome⟩ in rs do
        if (outcome.isExplicit || include_impl) && (outcome.isProven || include_conj) then
          if outcome.isTrue then println! s!"{lhs} → {rhs}"
          else println! s!"¬ ({lhs} → {rhs})"
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
