import Lean.Util.SearchPath
import Cli.Basic
import equational_theories.Equations.Command

open Lean Elab Meta Cli

/-!

# Exporting magma equations

This script exports all the magma equations defined in the input files as JSON to the standard
output. If no input files are specified, all equations in the project are included.

The format is
```
{
  "equation": "Equation4512",
  "law": {
    "lhs": {"left": {"leaf": 0}, "right": {"left": {"leaf": 1}, "right": {"leaf": 2}}},
    "rhs": {"left": {"left": {"leaf": 0}, "right": {"leaf": 1}}, "right": {"leaf": 2}}
  },
  "formatted": "0 ◇ (1 ◇ 2) ≃ (0 ◇ 1) ◇ 2"
}
```
-/

def exportEquations (inp : Cli.Parsed) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%
  let mut modules := inp.variableArgsAs! ModuleName
  if modules.isEmpty then
    modules := #[`equational_theories]
  let imports : Array Import := modules.map ({ module := · })
  let env ← importModules imports {} (trustLevel := 1024)
  let laws ← EIO.toIO (fun _ ↦ IO.userError "Failed to get magma laws.") <|
            getMagmaLaws.run' { fileName := "", fileMap := default } { env := env }
  let laws := laws
    |>.map (fun (lawName, law) => (lawName.toString.toSubstring.drop "Law".length |>.toNat?.get!, law))
    |>.qsort (fun (num1, _) (num2, _) => num1 < num2)
  let jsonOutput : Json := Json.arr <| laws.map fun ⟨lawNum, law⟩ => .mkObj [
    ("equation", s!"Equation{lawNum}"),
    ("law", toJson law),
    ("formatted", toJson (toString law))
  ]
  IO.println jsonOutput.pretty
  pure 0

def exportEquationsCmd : Cmd := `[Cli|
  export_equations VIA exportEquations;
  "Export the magma equations in a JSON format."

  ARGS:
    ...files : Array ModuleName; "The files to extract the implications from"
]

def main (args : List String) : IO UInt32 := do
  exportEquationsCmd.validate args
