import Lean
import equational_theories.RSimpSet
import equational_theories.Magma
import equational_theories.MemoFinOp

/-!
This module defines variants of the `decide` tactic with various hacks to speed up elaboration.
-/

open Lean Elab Tactic Meta

private def preprocessPropToDecide (expectedType : Expr) : TermElabM Expr := do
  let mut expectedType ← instantiateMVars expectedType
  if expectedType.hasFVar then
    expectedType ← zetaReduce expectedType
  if expectedType.hasFVar || expectedType.hasMVar then
    throwError "expected type must not contain free or meta variables{indentExpr expectedType}"
  return expectedType

private def splitConjs (e : Lean.Expr) : Array (Lean.Expr) := Id.run do
  let mut e := e
  let mut r := #[]
  while e.isAppOf `And do
    r := r.push e.appFn!.appArg!
    e := e.appArg!
  r := r.push e
  return r

/--
This is a variant of the `decide` tactic. It does not actually check the proposition at elaboration
time, and just assumes it is true.  This is useful in generated lean code, where we know it will
succeed, and we really just want the check done once, in the kernel.
-/
elab "decide!" : tactic => do
  closeMainGoalUsing `decide fun expectedType => do
    let expectedType ← preprocessPropToDecide expectedType
    let expectedTypes := splitConjs expectedType
    let proofs ← expectedTypes.mapM fun expectedType => do
      let d ← mkDecide expectedType
      let d ← instantiateMVars d
      -- Get instance from `d`
      let s := d.appArg!
      let rflPrf ← mkEqRefl (toExpr true)
      return mkApp3 (Lean.mkConst ``of_decide_eq_true) expectedType s rflPrf
    let proof ← proofs.pop.foldrM (mkAppM ``And.intro #[·, ·]) proofs.back
    return proof

private partial def inferDecideFin (p : Expr) : MetaM Expr := do
  let p ← whnfR p
  match p with
  | .forallE i d b bi =>
    match_expr (← whnfR d) with
    | Fin n =>
      let inst ← withLocalDeclD i d fun x => do
        let body := b.instantiate1 x
        let inst ← inferDecideFin body
        mkLambdaFVars #[x] inst
      return mkApp3 (mkConst ``Nat.decidableForallFin) n (.lam i d b bi) inst
    | _ => throwError "Expected Fin n quantifier"
  | _ =>
    match_expr p with
    | True =>
      return mkConst ``True.intro
    | Not p' =>
      let inst ← inferDecideFin p'
      return mkApp2 (mkConst ``instDecidableNot) p' inst
    | Eq t l r =>
      match_expr (← whnfR t) with
      | Fin n =>
        return mkApp3 (mkConst ``instDecidableEqFin) n l r
      | _ => throwError "Expected Fin n equality"
    | _ => throwError "Unsupported proposition {p}"


theorem of_opt_decide_eq_true {p : Prop} [inst : Decidable p] (c : Bool) (h : decide p = c)
  : c = true → p := by cases h; exact of_decide_eq_true

/-!
Like `decide!`, but only supports goals that are conjunctions of (possibly negations of) goals
of the form `∀ (x … z : Fin n), lhs = rhs`.

Using type class synthesis to infer the decidability instances can be very slow, slower than the
actual proof checking, so this tactic constructs the instances very directly.
-/
elab "decideFin!" : tactic => do
  closeMainGoalUsing `decideFin fun expectedType => do
    let expectedType ← preprocessPropToDecide expectedType
    let expectedTypes := splitConjs expectedType
    let proofs ← expectedTypes.mapM fun expectedType => do
      let s ← inferDecideFin expectedType
      let decE := mkApp2 (mkConst ``decide) expectedType s
      let .some se ← getSimpExtension? `rsimp | throwError "simp set rsimp not found"
      let ctx := { config := {}, simpTheorems := #[(← se.getTheorems)], congrTheorems := (← Meta.getSimpCongrTheorems) }
      let (res, _stats) ← simp decE ctx
      let optE := res.expr
      let optPrf ← res.getProof
      let rflPrf ← mkEqRefl (toExpr true)
      return mkApp5 (Lean.mkConst ``of_opt_decide_eq_true) expectedType s optE optPrf rflPrf
    let proof ← proofs.pop.foldrM (mkAppM ``And.intro #[·, ·]) proofs.back
    return proof

-- Setup to optimze the kind of terms we evaluate

def Fin.all {n : Nat} (P : ∀ i < n, Bool) : Bool := go n (Nat.le_refl n)
  where
  go := Nat.rec
    (motive := fun i => i ≤ n → Bool)
    (fun _ => true)
    (fun i ih p => P i (by omega) && ih (by omega))

def Nat.all_below (n : Nat) (P : Nat → Bool) : Bool :=
  Nat.rec true (fun i ih => P i && ih) n

@[rsimp]
def Fin.all_eq_all_below {n : Nat} (P : ∀ i < n, Bool) (P' : Nat → Bool)
  (hP : ∀  i h, P i h = P' i) : Fin.all P = Nat.all_below n P' := by
  suffices ∀ i (h : i ≤ n), Fin.all.go P i h = Nat.all_below i P'
    by apply this
  intros i h
  induction i
  case zero => rfl
  case succ i ih =>
    simp [all.go, Nat.all_below]
    congr
    · apply hP
    · apply ih


theorem Bool.eq_of_eq_true_iff_eq_true {a b : Bool} : (a = true ↔ b = true) → a = b := by
  cases a; cases b
  all_goals simp

@[rsimp]
theorem Fin.decideAll_to_Fin.all {n : Nat} {P : Fin n → Prop} [DecidablePred P] :
    decide (∀ x, P x) = Fin.all (fun i h => decide (P ⟨i, h⟩)) := by
  apply Bool.eq_of_eq_true_iff_eq_true
  simp [Fin.all]
  suffices ∀ i (h : i ≤ n), (∀ j (hj : j < i), P ⟨j, by omega⟩) = all.go (fun i h ↦ decide (P ⟨i, h⟩)) i h by
    rw [← this n (Nat.le_refl n)]
    exact forall_iff
  intro i h
  induction i
  case a.zero =>
    simp [all.go]
    rfl
  case a.succ i ih =>
    apply propext
    calc (∀ (j : Nat) (hj : j < i + 1), P ⟨j, by omega⟩)
      _ ↔ P ⟨i, h⟩ ∧ (∀ (j : Nat) (hj : j < i), P ⟨j, by omega⟩) := by
        constructor
        · exact fun h' => ⟨h' i (by omega), fun j hj => h' j (by omega)⟩
        · intro h' j hj
          by_cases j = i
          · subst j; apply h'.1
          · apply h'.2 j (by omega)
      _ ↔ decide (P ⟨i, h⟩) = true ∧ (∀ (j : Nat) (hj : j < i), P ⟨j, by omega⟩) := by simp
      _ ↔ decide (P ⟨i, h⟩) = true ∧ all.go (fun i h ↦ decide (P ⟨i, h⟩)) i (by omega) = true := by rw [ih]
      _ ↔ all.go (fun i h ↦ decide (P ⟨i, h⟩)) (i+1) h = true := by simp [all.go]

@[rsimp]
theorem Fin.decideEq_to_Nat {n : Nat} {x y : Fin n} :
    decide (x = y) = decide (x.val = y.val) := by
  simp [Fin.ext_iff]

@[rsimp]
theorem Nat.decideEq_to_beq {x y : Nat} :
    decide (x = y) = (Nat.beq x y) := by
  simp [decide, instDecidableEqNat, Nat.decEq]
  split
  · simp [*]
  · simp [*]

attribute [rsimp] Magma.op MemoFinOp.opOfTable

attribute [rsimp] Nat.decideEq_to_beq
attribute [rsimp] Fin.val_mul Fin.val_add Mul.mul Fin.mul
attribute [rsimp] instHAdd instHMul instAddNat instMulNat instHPow instPowNat instNatPowNat
attribute [rsimp] instHMod Nat.instMod instHDiv Nat.instDiv


namespace Example
def table : Nat := 176572862725894008122698639442158340463570358062018791456284713065412594783123644086682432661794684073102303331486778326370940525772356431236683795848309863276639424307474540043134479302998

abbrev Equation2531 (G: Type _) [Magma G] := ∀ x y : G, x = (y ◇ ((y ◇ x) ◇ x)) ◇ y

@[rsimp]
def M2 : Magma (Fin 13) where
  op := MemoFinOp.opOfTable table

theorem Equation2531_M2 : @Equation2531 (Fin 13) M2 := by
  -- show_term
  decideFin!

end Example
