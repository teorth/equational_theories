import Lean

/-!
This file defines a macro `memoFinOp` that takes a function `f : Fin n → Fin n → Fin n`, at
elaboration time calculates its table of values, encodes it into a single `Nat`, and returns a term
that implements the operation via lookup in this table.
-/

open Lean Meta Elab  Term

def opOfTable {n : Nat} (t : Nat) (a : Fin n) (b : Fin n) : Fin n :=
  let i := a.val * n + b.val
  let r := (t / n^i) % n
  ⟨r, Nat.mod_lt _ (by exact Fin.pos a)⟩

/-- `enum n` is the array of all elements of `Fin n` in order -/
private def Fin.enum (n) : Array (Fin n) := Array.ofFn id

def buildMemo {n : Nat} (f : Fin n → Fin n → Fin n) : Nat := Id.run do
  let mut t := 0
  for a in Fin.enum n do
    for b in Fin.enum n do
      let i := a.val * n + b.val
      t := t + f a b * n^i
  t

-- Quick sanity check:
example :
    let f := fun (a b : Fin 4) => a * a * b + 2
    opOfTable (buildMemo f) = f := by
  funext a b; revert a b; native_decide

@[implemented_by Meta.evalExpr]
private opaque myEvalExpr (α) (expectedType : Expr) (value : Expr) (safety := DefinitionSafety.safe) : MetaM α

elab "memoFinOp" fn:term:arg :term <= expectedType? => do
  let fn ← elabTerm fn expectedType?
  Term.synthesizeSyntheticMVarsNoPostponing
  if (← Term.logUnassignedUsingErrorInfos (← getMVars fn)) then throwAbortTerm

  -- Type checking
  let type ← inferType fn
  let type ← instantiateMVars type
  unless type.isForall do
    throwError "expected a function, got {type}"
  let t := type.bindingDomain!
  unless t.isAppOfArity ``Fin 1 do
    throwError "expected a function of Fin n for some n"
  let nE ← instantiateMVars t.appArg!
  -- let .lit (.natVal _) := nE
  --  | throwError "expected a function of Fin n for a concrete n, got {nE}"
  let expectedType := .forallE `a t (.forallE `b t t .default) .default
  unless (← isDefEq type  expectedType ) do
    throwError "expected type {expectedType}, got {type}"

  let eval ← instantiateMVars (mkApp2 (mkConst ``buildMemo) nE fn)
  if eval.hasMVar then
    throwError "cannot evaluate expression {eval}, it contains metavariables"
  let t ← myEvalExpr Nat (mkConst ``Nat) eval

  return mkApp2 (mkConst ``opOfTable) nE (.lit (.natVal t))

set_option pp.instantiateMVars false

example :
    memoFinOp (fun (a b : Fin 4) => a * a * b + 2) = (fun (a b : Fin 4) => a * a * b + 2) := by
  funext a b; revert a b; native_decide
