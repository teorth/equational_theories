import equational_theories.EquationalResult
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.FiniteModel
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Units
import Mathlib.Data.Nat.ModEq
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith

namespace Eq3342

def op (a b : Option (ℕ × ℕ)) : Option (ℕ × ℕ) :=
  match a, b with
  | some (a, b),  some (c, d) =>
    if b = d ∧ (a = c ∨ a + 1 = c) then (0, b + 1) else
    if b + 1 = d ∧ a ≥ c then (a-c+1, b) else
    if b = d + 1 ∧ a < c then (c-a, d) else
    none
  | _, _ => none

@[equational_result]
theorem Equation3342_facts : ∃ (G : Type) (_ : Magma G), Facts G [3342] [3456, 3522, 4065, 4118] := by
  use Option (ℕ × ℕ), ⟨op⟩
  split_ands
  · intro x y
    cases x
    cases y
    · rfl
    · rfl
    cases y
    · rfl
    · simp [op]
      split_ifs
      · simp_all
      · simp_all
      · simp_all
      · omega
      · simp_all
      · omega
      · simp only [Option.some.injEq, Prod.mk.injEq, and_true]
        omega
      · omega
      · omega
      · simp only [Option.some.injEq, Prod.mk.injEq, and_true]
        omega
      · simp only [Option.some.injEq, Prod.mk.injEq]
        omega
      · omega
      · omega
      · omega
      · omega
      · rfl
  · simp only [not_forall]
    use (0, 0)
    decide
  · simp only [not_forall]
    use (0, 0), (0, 0)
    decide
  · simp only [not_forall]
    use (0, 0)
    decide
  · simp only [not_forall]
    use (0, 0), (0, 0)
    decide

-- https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Austin.20pairs/near/482525422

private theorem main_result (G : Type*) [Magma G] [Finite G] (h : Equation3342 G) :
    Equation3522 G ∧ Equation4118 G := by
  let S (x : G) := x ◇ x
  let f (x : G) := x ◇ (S x)
  let C (x : G) := (S x) ◇ x
  obtain ⟨p, hpgt, hperiodic⟩ := FiniteModel.Finite.fn_eventually_periodic' f
  have fx_fy (x y : G) : x ◇ y = f x ◇ f y := by rw [h, h]
  have fnx_fny (n : ℕ) (x y : G) : x ◇ y = f^[n] x ◇ f^[n] y := by
    induction n with
    | zero => simp only [Function.iterate_zero, id]
    | succ n ih =>
      rw [ih, fx_fy, Function.Commute.self_iterate f, Function.Commute.self_iterate f]
      simp only [Function.iterate_succ, Function.comp_apply, hpgt]
  have y_fx (x y : G) : x ◇ y = y ◇ f x := by rw [h]
  have Sx_Sfx (n : ℕ) (x y : G) : S x = S (f^[n] x) := by
    induction n with
    | zero => simp only [Function.iterate_zero, id_eq]
    | succ n ih =>
      rw [ih]
      unfold S
      rw [fx_fy]
      change S (f (f^[n] x)) = S (f^[n + 1] x)
      rw [Function.Commute.self_iterate f, ← Function.iterate_succ_apply, Nat.succ_eq_add_one]
  have Cx_fnx (x : G) : C x = f^[p] x := by
    calc
      C x = S x ◇ x := by simp only [C]
      _ = f^[p] (S x) ◇ f^[p] x := by rw [fnx_fny]
      _ = f^[p] (S x) ◇ f^[2*p] x := by rw [← hperiodic]
      _ = f^[2*p - 1] x ◇ f^[p] (S x) := by
        nth_rewrite 2 [y_fx]
        rw [Function.Commute.self_iterate f, ← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_one_add_one]
        linarith
      _ = f^[p - 1] x ◇ (S x) := by
        have : 2*p - 1 = p + (p - 1) := by omega
        rw [this, Function.iterate_add_apply, ← fnx_fny p]
      _ = f (f^[p - 1] x) := by rwa [Sx_Sfx (p - 1)]
      _ = f^[p] x := by
        rw [Function.Commute.self_iterate f, ← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_one_add_one]
        linarith
  constructor
  . intro x y
    have : x ◇ C y = x ◇ y := by
      calc
        x ◇ C y = x ◇ f^[p] y := by rw [Cx_fnx]
        _ = f^[p] x ◇ f^[2*p] y := by rw [fnx_fny p, ← Function.iterate_add_apply, ← Nat.two_mul]
        _ = f^[p] x ◇ f^[p] y := by rw [← hperiodic]
        _ = x ◇ y := by rw [← fnx_fny]
    exact Eq.symm this
  . intro x y
    have : C x ◇ y = x ◇ y := by
      calc
        C x ◇ y = f^[p] x ◇ y := by rw [Cx_fnx]
        _ = f^[2*p] x ◇ f^[p] y := by rw [fnx_fny p, ← Function.iterate_add_apply, ← Nat.two_mul]
        _ = f^[p] x ◇ f^[p] y := by rw [← hperiodic]
        _ = x ◇ y := by rw [← fnx_fny]
    exact Eq.symm this

@[equational_result]
theorem Finite.Equation3342_implies_Equation3522 (G : Type*) [Magma G] [Finite G] (h : Equation3342 G) :
    Equation3522 G := by
  exact (main_result G h).left

@[equational_result]
theorem Finite.Equation3342_implies_Equation4118 (G : Type*) [Magma G] [Finite G] (h : Equation3342 G) :
    Equation4118 G := by
  exact (main_result G h).right

end Eq3342
