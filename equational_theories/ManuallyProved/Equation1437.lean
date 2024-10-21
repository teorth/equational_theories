import equational_theories.EquationalResult
import equational_theories.Equations.All
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Ring.Nat

namespace Eq1437

def op (a b : ℕ × Fin 3) : ℕ × Fin 3 :=
  (if a.2 = b.2 + 2 then
      (if a.1 = 0 then b.1 else a.1 - 1)
    else a.1 + 1,
    b.2 + 1)

@[equational_result]
theorem _root_.Equation1437_not_implies_Equation4269 : ∃ (G : Type) (_ : Magma G), Equation1437 G ∧ ¬ Equation4269 G := by
  use ℕ × Fin 3, ⟨op⟩
  constructor
  · intro x y z
    simp [op, add_assoc]
  · simp only [not_forall, op]
    use (0, 0), (2, 0)
    decide

end Eq1437
