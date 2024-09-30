import equational_theories.Closure

open Lean Core Elab Result Closure

unsafe def generateOutput : IO Unit := do
  let module := `equational_theories
  searchPathRef.set compile_time_search_path%

  withImportModules #[{module}] {} (trustLevel := 1024) fun env =>
    let ctx := {fileName := "", fileMap := default}
    let state := {env}
    Prod.fst <$> (Meta.MetaM.toIO · ctx state)  do
      let rs ← collectClosure
      for ⟨⟨lhs, rhs⟩, out⟩ in rs do
        println! "{lhs} → {rhs}: {out}"

unsafe def main (_args : List String) : IO Unit := do
  generateOutput
