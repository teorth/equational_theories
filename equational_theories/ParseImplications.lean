import Lean.Environment
import Lean.Meta.Basic
import Lean.Util

open Lean

/--
`lhs` implies `rhs`, where `lhs` and `rhs` are equation names for the form "Equation17".
-/
structure Implication where
  lhs : String
  rhs : String
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

/--
Attempts to parse theorem type as an unconditional equation.
-/
def parseUnconditionalEquation (thm_ty : Expr) : MetaM (Option String) := do
  Meta.forallTelescope thm_ty fun fvars rhs => do
    let #[g, magma] := fvars | return none
    if !(← Meta.isType g) then return none
    let (.app (.const `Magma _) _) := ← Meta.inferType magma | return none
    return getEquationName rhs
