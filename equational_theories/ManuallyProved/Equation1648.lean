import Mathlib.Tactic
import equational_theories.Equations.Eqns1_999
import equational_theories.Equations.Eqns1000_1999

def sign (x : ℤ) :=
  if x = 0 then 0 else if x < 0 then -1 else 1

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

theorem Equation1648_not_implies_Equation151 : ∃ (G: Type) (_: Magma G),
  Equation1648 G ∧ ¬ Equation151 G := by
  let instMagmaInt : Magma ℤ := {
    op := fun x y => if x > y then x + 1 else x - 1
  }
  use ℤ, instMagmaInt
  simp only [Equation1648, Equation151, not_forall]

  constructor
  · intro x y
    simp only [gt_iff_lt, instMagmaInt]
    split <;> simp <;> split <;> simp_all <;> linarith
  · simp only [gt_iff_lt, lt_self_iff_false, ↓reduceIte, instMagmaInt]
    use 0
    simp
