import Lean

/-!
This file defines the macro `memoFinOp` that memoizes a function `f : Fin n → Fin n → Fin n`; see
its docstring for more info.
-/

namespace MemoFinOp

open Lean Meta Elab Term

def opOfTable {n : Nat} (t : Nat) (a : Fin n) (b : Fin n) : Fin n :=
  let i := a.val * n + b.val
  let r := (t / n^i) % n
  ⟨r, Nat.mod_lt _ (Fin.pos a)⟩

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

private unsafe def evalNatImpl (e : Expr) : MetaM Nat := do
  let t ← inferType e
  unless t.isConstOf ``Nat do
    throwError "evalNat: expected expression of type `Nat`, but got {t}"
  let e ← instantiateMVars e
  if e.hasExprMVar then
    throwError "evalNat: cannot evaluate expression{indentExpr e}\nit contains metavariables"
  evalExpr Nat (mkConst ``Nat) e

@[implemented_by evalNatImpl]
private opaque evalNat (value : Expr) : MetaM Nat

/-
The syntax `memoFinOp f` takes a function `f : Fin n → Fin n → Fin n` and implements it in a
kernel-reduction friendly way.

More precisely, it tabulates all values of `f` at elabortion time and encodes that table into a
single `Nat`, which it queries using `/` and `%`. This should perform decenetly well in compiled
code, and make a big difference when using kernel reduction (e.g. `by decide`) because efficient
arrays are not available there.
-/
elab "memoFinOp" fn:term:arg :term <= expectedType? => do
  let fn ← elabTermAndSynthesize fn expectedType?
  Term.synthesizeSyntheticMVarsNoPostponing
  if (← Term.logUnassignedUsingErrorInfos (← getMVars fn)) then throwAbortTerm
  let fn ← zetaReduce fn

  -- Type checking
  let type ← inferType fn
  let type ← instantiateMVars type
  unless type.isForall do
    throwError "expected a function, got {type}"
  let t := type.bindingDomain!
  unless t.isAppOfArity ``Fin 1 do
    throwError "expected a function of Fin n for some n"
  let nE ← instantiateMVars t.appArg!
  let expectedType := .forallE `a t (.forallE `b t t .default) .default
  unless (← isDefEq type expectedType ) do
    throwError "expected type {expectedType}, got {type}"

  -- Tabulation
  let table ← evalNat (mkApp2 (mkConst ``buildMemo) nE fn)
  return mkApp2 (mkConst ``opOfTable) nE (.lit (.natVal table))

example :
    let f := fun (a b : Fin 4) => a * a * b + (2 : Fin 4)
    memoFinOp f = f := by
  funext a b; revert a b; decide

end MemoFinOp
