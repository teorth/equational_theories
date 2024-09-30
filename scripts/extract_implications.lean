import Lean.Meta.Basic
import Lean.Util
import equational_theories.EquationalResult

open Lean Core Elab

--- Output of the extract_implications executable.
structure Output where
  implications : Array Implication
  nonimplications : Array Implication
  unconditionals : Array String
deriving Lean.ToJson, Lean.FromJson

def main (args : List String) : IO Unit := do
  let module := ← match args with
    | [] => pure `equational_theories
    | [mod] => pure mod.toName
    | _ => throw <| IO.userError "usage: extract_implications MODULE"

  searchPathRef.set compile_time_search_path%

  unsafe withImportModules #[{module}] {} (trustLevel := 1024) fun env =>
    let ctx := {fileName := "", fileMap := default}
    let state := {env}
    Prod.fst <$> (Meta.MetaM.toIO · ctx state) do
      let rs ← Result.extractTheorems
      let mut implications : Array Implication := #[]
      let mut nonimplications : Array Implication := #[]
      let mut unconditionals : Array String := #[]
      for ⟨_name, _filename, res, _⟩ in rs do
        match res with
        | .implication imp => implications := implications.push imp
        | .nonimplication nimp => nonimplications := nonimplications.push nimp
        | .unconditional s => unconditionals := unconditionals.push s
      IO.println (Lean.toJson (Output.mk implications nonimplications unconditionals)).pretty
