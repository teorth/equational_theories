-- https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/1648.20!.3D.3E.20206/near/476775769

import Mathlib.Tactic
import equational_theories.EquationalResult
import equational_theories.Equations.All
import equational_theories.FactsSyntax

def sign (x : ℤ) :=
  if x = 0 then 0 else if x < 0 then -1 else 1

@[equational_result]
theorem Equation1648_not_implies_Equation206 : ∃ (G: Type) (_: Magma G),
  Equation1648 G ∧ ¬ Equation206 G := by
  let instMagmaInt : Magma ℤ := {
    op := fun x y => x - sign (y -x)
  }
  use ℤ, instMagmaInt
  constructor
  · intro x y
    have hop : ∀ a b : ℤ, a ◇ b = a - sign (b - a) := fun _ _ => rfl
    rw [hop, hop, hop]
    simp only [sub_sub_cancel_left]
    unfold sign
    split <;> simp_all
    case isFalse =>
      split <;> split <;> split <;> simp_all <;> omega
  · intro h
    have hop : ∀ a b : ℤ, a ◇ b = a - sign (b - a) := fun _ _ => rfl
    have := h 0 (-1)
    rw [hop, hop, hop] at this
    revert this
    decide

@[equational_result]
theorem Equation1648_facts : ∃ (G : Type) (_ : Magma G), Facts G [1648] [151, 203, 307, 1426, 1832, 2238, 2441, 3050, 3456, 3522, 4065] := by
  let instMagmaInt : Magma ℤ := {
    op := fun x y => if x > y then x + 1 else x - 1
  }
  use ℤ, instMagmaInt
  have hop : ∀ a b : ℤ, a ◇ b = if a > b then a + 1 else a - 1 := fun _ _ => rfl
  constructor
  · intro x y
    rw [hop, hop, hop]
    split <;> simp <;> split <;> simp_all <;> linarith
  · repeat' apply And.intro
    all_goals {
      by_contra h
      try specialize h 0 1
      try specialize h 0
      simp [hop] at h
    }
