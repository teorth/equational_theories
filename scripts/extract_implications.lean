import Batteries.Data.Array.Basic
import Batteries.Tactic.Lint.Frontend
import Cli.Basic
import equational_theories.ParseImplications
import Lean.Util.SearchPath

open Lean Core Elab Cli

--- Output of the extract_implications executable.
structure Output where
  implications : List Implication
  nonimplications : List Implication
deriving Lean.ToJson, Lean.FromJson

def generateOutput (inp : Cli.Parsed) : IO UInt32 := do
  let modules := inp.variableArgsAs! ModuleName
  if modules.isEmpty then
    inp.printHelp
    return 1
  searchPathRef.set compile_time_search_path%

  unsafe withImportModules (modules.map ({module := ·})) {} (trustLevel := 1024) fun env =>
    let ctx := {fileName := "", fileMap := default}
    let state := {env}
    Prod.fst <$> (Meta.MetaM.toIO · ctx state) do
      let decls := (← modules.mapM (Batteries.Tactic.Lint.getDeclsInPackage ·)).join
      let mut implications : List Implication := []
      let mut nonimplications : List Implication := []
      for d in decls do
        if not d.isInternal then
          match ← getConstInfo d with
          | .thmInfo thm =>
            -- TODO check axioms for `sorry`
            if let some imp ← parseImplication thm.type then
              implications := imp :: implications
            if let some nimp ← parseNonimplication thm.type then
              nonimplications := nimp :: nonimplications
            pure ()
          | _ => pure ()
      println! (Lean.toJson (Output.mk implications nonimplications)).pretty
      pure 0

def extract_implications : Cmd := `[Cli|
  extract_implications VIA generateOutput;
  "Extract the implications explicitly proven in the mentioned files."

  ARGS:
    ...files : Array ModuleName; "The files to extract the implications from"
]

def main (args : List String) : IO UInt32 := do
  extract_implications.validate args
