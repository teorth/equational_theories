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
deriving Lean.ToJson, Lean.FromJson, DecidableEq, Hashable

/--
Names of equations satisfied rsp. refuted by the same magma; used to concisely express
antiimplications.

For example, if `satisfied = [1, 2]` and `refuted = [4, 5]`, then this expresses
the four antiimplications `¬ 1→4`, `¬ 1→5`, `¬ 2→4`, `¬ 2→5`.
-/
structure Facts where
  satisfied : Array String
  refuted : Array String
deriving Lean.ToJson, Lean.FromJson, Inhabited

/--
Extracts the equation name out of an expression of the form `EquationN G inst`.
-/
def getEquationName (app : Expr) : Option String := do
  match app with
  | (.app (.app (.const name _) _) _) =>
    -- Copy the string to allow it to safely escape from `Lean.withImportModules`.
    -- Otherwise, segfaults are possible.
    some ("" ++ name.toString)
  | _ => none

def isCoreEquationName (s : String) : Bool := Id.run do
  if !s.startsWith "Equation" then return false
  let some n := (s.toSubstring.drop 8).toNat? | return false
  return 0 < n && n <= 4694

def filterCoreEquationName (s : String) : Option String :=
  if isCoreEquationName s then some s else none

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
Attempts to parse an exisential statement of monoid facts from the type of a theorem.
-/
partial def parseFacts (thm_ty : Expr) : MetaM (Option Facts) := do
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
          let some facts := go #[ty1] #[] #[] | return none
          if facts.satisfied.isEmpty && facts.refuted.isEmpty then return none
          return .some facts
      | _ => return none
  | _ => return none
where
  -- NB: This is written as a tail-recursive function, else some large facts statements
  -- cause this to blow the stack
  go (todo : Array Expr) (satisfied refuted : Array String) : Option Facts := do
    if todo.isEmpty then
      return ⟨satisfied, refuted⟩
    else
      let e := todo.back
      let todo := todo.pop
      if e.isAppOfArity ``And 2 then
        go ((todo.push e.appFn!.appArg!).push e.appArg!) satisfied refuted
      else if e.isAppOfArity ``Not 1 then
        let name ← getEquationName e.appArg!
        go todo satisfied (refuted.push name)
      else
        let name ← getEquationName e
        go todo (satisfied.push name) refuted

/--
Attempts to parse theorem type as an unconditional equation.
-/
def parseUnconditionalEquation (thm_ty : Expr) : MetaM (Option String) := do
  Meta.forallTelescope thm_ty fun fvars rhs => do
    let #[g, magma] := fvars | return none
    if !(← Meta.isType g) then return none
    let (.app (.const `Magma _) _) := ← Meta.inferType magma | return none
    return getEquationName rhs
