import equational_theories.Closure

open Lean Core Elab Result Closure

unsafe def generateOutput : IO Unit := do
  let module := `equational_theories
  searchPathRef.set compile_time_search_path%

  withImportModules #[{module}] {} (trustLevel := 1024) fun env =>
    let ctx := {fileName := "", fileMap := default}
    let state := {env}
    Prod.fst <$> (Meta.MetaM.toIO · ctx state)  do
      IO.eprintln "Running"
      let rs ← extractResults
      IO.eprintln s!"Running {rs.size}"
      let rs' : Array EntryVariant ← closure (rs.map Entry.variant)
      for res in rs' do
        match res with
        | .implication ⟨lhs, rhs⟩ => println! "{lhs} → {rhs}"
        | .nonimplication ⟨lhs, rhs⟩ => println! "¬ ({lhs} → {rhs})"

unsafe def main (_args : List String) : IO Unit := do
  generateOutput
