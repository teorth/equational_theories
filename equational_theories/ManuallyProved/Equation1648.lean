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
  simp only [Equation1648, Equation206, not_forall]
  constructor
  · intro x y
    simp only [sign, sub_neg, Int.reduceNeg, sub_sub_cancel_left, neg_eq_zero, ite_eq_left_iff,
      sub_lt_self_iff, instMagmaInt]
    split <;> try simp_all
    case h.left.isFalse =>
      split <;> split <;> split <;> simp_all <;> linarith
  · use 0,-1
    simp only [sign, sub_neg, Int.reduceNeg, sub_zero, neg_eq_zero, one_ne_zero, ↓reduceIte,
      Left.neg_neg_iff, zero_lt_one, sub_neg_eq_add, zero_add, Int.reduceLT, zero_sub, sub_self,
      zero_eq_neg, not_false_eq_true, instMagmaInt]

@[equational_result]
theorem Equation1648_facts : ∃ (G : Type) (_ : Magma G), Facts G [1648] [151, 203, 307, 1426, 1832, 2238, 2441, 3050, 3456, 3522, 4065] := by
  let instMagmaInt : Magma ℤ := {
    op := fun x y => if x > y then x + 1 else x - 1
  }
  use ℤ, instMagmaInt

  constructor
  · intro x y
    simp only [gt_iff_lt, instMagmaInt]
    split <;> simp <;> split <;> simp_all <;> linarith
  · repeat' apply And.intro
    all_goals {
      by_contra h
      try specialize h 0 1
      try specialize h 0
      simp [instMagmaInt] at h
    }
