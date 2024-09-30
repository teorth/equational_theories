import Lean.Meta.Basic
import Lean.Util
import equational_theories.EquationalResult

open Lean Core Elab

unsafe def main (args : List String) : IO Unit := do
  let module := ← match args with
    | [] => pure `equational_theories
    | [mod] => pure mod.toName
    | _ => throw <| IO.userError "usage: extract_implications MODULE"

  searchPathRef.set compile_time_search_path%

  withImportModules #[{module}] {} (trustLevel := 1024) fun env =>
    let ctx := {fileName := "", fileMap := default}
    let state := {env}
    Prod.fst <$> (Meta.MetaM.toIO · ctx state)  do
      println! (Lean.toJson (← Result.collectResults)).pretty
