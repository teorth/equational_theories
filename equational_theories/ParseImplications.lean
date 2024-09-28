import Batteries.Data.String.Basic
import Batteries.Tactic.Lint
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util

open Lean Core Elab

/--
`lhs` implies `rhs`, where `lhs` and `rhs` are equation names for the form "Equation17".
-/
structure Implication where
  lhs : String
  rhs : String
deriving Lean.ToJson, Lean.FromJson

--- Output of the extract_implications executable.
structure Output where
  implications : List Implication
  nonimplications : List Implication
deriving Lean.ToJson, Lean.FromJson

/--
Extracts the equation name out of an expression of the form `EquationN G inst`.
-/
def getEquationName (app : Expr) : Option String := do
  match app with
  | (.app (.app (.const name _) _) _) => some ("" ++ name.toString)
  | _ => none

/--
Extracts an `Implication` from two expressions of the form `EquationN G inst`.
-/
def implicationFromApps (lhs rhs : Expr) : Option Implication := do
  let lhsName ← getEquationName lhs
  let rhsName ← getEquationName rhs
  return ⟨lhsName, rhsName⟩

/--
Attempts to parse an `Implication` from the type of a theorem.
-/
def parseImplication (thm_ty : Expr) : MetaM (Option Implication) := do
  Meta.forallTelescope thm_ty fun fvars rhs => do
    let #[g, magma, lhsv] := fvars | return none
    if !(← Meta.isType g) then return none
    let (.app (.const `Magma _) _) := ← Meta.inferType magma | return none
    let lhs ← Meta.inferType lhsv
    return implicationFromApps lhs rhs

/--
Attempts to parse a negated `Implication` from the type of a theorem.
-/
def parseNonimplication (thm_ty : Expr) : MetaM (Option Implication) := do
  match_expr thm_ty with
  | Exists b body =>
    if !(← Meta.isType b) then return none
    Meta.lambdaTelescope body fun fvars ty => do
      let #[g] := fvars | return none
      if !(← Meta.isType g) then return none
      match_expr ty with
      | Exists b1 body1 =>
        let (.app (.const `Magma _) _) := b1 | return none
        Meta.lambdaTelescope body1 fun fvars1 ty1 => do
          let #[magma] := fvars1 | return none
          let (.app (.const `Magma _) _) := ← Meta.inferType magma | return none
          match_expr ty1 with
          | And rhs b =>
            match_expr b with
            | Not lhs =>
              return implicationFromApps lhs rhs
            | _ => return none
          | _ => return none
      | _ => return none
  | _ => return none

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
