import Mathlib.Tactic
import equational_theories.Equations.Eqns1_999
import equational_theories.Equations.Eqns1000_1999

def sign (x : ℤ) :=
  if x = 0 then 0 else if x < 0 then -1 else 1

theorem Equation1648_not_implies_Equation206 : ∃ (G: Type) (_: Magma G), Equation1648 G ∧ ¬ Equation206 G := by
  let instMagmaInt : Magma ℤ := {
    op := fun x y => x - sign (y -x)
  }
  use ℤ, instMagmaInt
  simp [Equation1648, Equation206]
  constructor
  · intro x y
    simp [instMagmaInt, sign]
    split <;> try simp_all
    case h.left.isFalse =>
      split <;> simp_all <;> split <;> split <;> simp_all <;> linarith
  · use 0,-1
    simp [instMagmaInt, sign]
