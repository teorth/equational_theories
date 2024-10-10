import equational_theories.Equations
import equational_theories.AllEquations

open Lean Elab Command Meta

def main : IO Unit := do
  searchPathRef.set compile_time_search_path%
  let env ← importModules #[
    { module := `equational_theories.Equations },
    { module := `equational_theories.AllEquations }] .empty
  let laws ← EIO.toIO (fun _ ↦ IO.userError "Failed to get magma laws.") <|
            getMagmaLaws.run' { fileName := "", fileMap := default } { env := env }
  let jsonOutput : Json := Json.arr <| laws.map fun ⟨lawName, law⟩ => .mkObj [
    ("equation", magmaLawNameToEquationName lawName.toString),
    ("law", ToJson.toJson law)
  ]
  IO.FS.writeFile ("data" / "magma_equations.json") jsonOutput.pretty
