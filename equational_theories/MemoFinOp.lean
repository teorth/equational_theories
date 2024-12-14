import Lean

/-!
This file defines the macro `memoFinOp` that memoizes a function `f : Fin n → Fin n → Fin n`; see
its docstring for more info.

The `finOpTable` macro is intended to replace `memoFinOp` as it's faster for large tables, but
FinitePoly still requires the `memoFinOp` style.
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

-- https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Austin.20pairs/near/486226698

-- assume each nat is ≤ 256
def rowToNat (row : List Nat) : Nat :=
  match row with
  | [] => 0
  | n :: ns => n + 256 * rowToNat ns

def extract (matrix : List Nat) (row col : Nat) : Nat :=
  255 &&& ((List.get! matrix row) >>> (col * 8))

def IsTable (n : Nat) (matrix : List Nat) : Prop :=
  ∀ x y : Fin n, extract matrix x y < n

instance decidableIsTable {n matrix} : Decidable (IsTable n matrix) := by
  unfold IsTable
  infer_instance

def extractWrapper (n : Nat) (matrix : List Nat) (h : IsTable n matrix) (row col : Fin n) : Fin n :=
  ⟨extract matrix row.val col.val, h row col⟩

open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parseArray {α : Type} (p : Parser α) : Parser (List α) := do
  ws *> skipChar '['
  let arr ← many (ws *> p <* optional (ws *> skipChar ','))
  ws *> skipChar ']'
  return arr.toList

def parseData (data : String) : IO (List (List Nat)) := do
  match parseArray (parseArray digits) (String.mkIterator data) with
  | .success _ v => return v
  | .error _ err => throw <| IO.userError err

/-
`finOpTable "[[0,1],[1,0]"` returns a method to compute the operation encoded by a given table, in
a method specifically intended to be efficient for large tables.
-/
elab "finOpTable" str:str :term => do
  let matrix ← parseData str.getString
  guard <| matrix.length < 256
  guard <| matrix.all (·.length == matrix.length)
  let table := toExpr (matrix.map rowToNat)
  let istable := mkApp2 (mkConst ``IsTable) (mkLit (.natVal matrix.length)) table
  let mv ← mkFreshExprMVar istable
  discard <| withCurrHeartbeats <| Tactic.run mv.mvarId! do Lean.Elab.Tactic.evalTactic (← `(tactic| decide +kernel))
  return mkApp3 (mkConst ``extractWrapper) (mkLit (.natVal matrix.length)) table (← instantiateMVars mv)

end MemoFinOp
