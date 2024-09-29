import equational_theories.ParseImplications

open Lean Core Elab

unsafe def generateOutput : IO Output := do
  let module := `equational_theories.Subgraph
  searchPathRef.set compile_time_search_path%

  withImportModules #[{module}] {} (trustLevel := 1024) fun env =>
    let ctx := {fileName := "", fileMap := default}
    let state := {env}
    Prod.fst <$> (Meta.MetaM.toIO · ctx state)  do
      let decls ← Batteries.Tactic.Lint.getDeclsInPackage module
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
      pure ⟨implications, nonimplications⟩

unsafe def main (_args : List String) : IO Unit := do
  println! (Lean.toJson (← generateOutput)).pretty
