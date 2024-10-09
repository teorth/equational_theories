import equational_theories.Equations
import equational_theories.Equations.All

open Lean Elab Command Meta

/-!

# Exporting magma equations

This script exports all the magma equations defined in the `Equations` and `AllEquations` files
to the JSON file `data/magma_equations.json`.

The format is
```
{
  "equation": "EquationName",
  "law": {
    "lhs": { ... },
    "rhs": { ... }
  }
}
-/

def main : IO Unit := do
  searchPathRef.set compile_time_search_path%
  let env ← importModules #[
    { module := `equational_theories.Equations },
    { module := `equational_theories.Equations.All }] .empty
  let laws := magmaLawExt.getState env
  let jsonOutput : Json := Json.arr <| laws.map fun ⟨lawName, law⟩ => .mkObj [
    ("equation", "Equation" ++ (lawName.toString.drop "Law".length)),
    ("law", ToJson.toJson law)
  ]
  IO.FS.writeFile ("data" / "magma_equations.json") jsonOutput.pretty
