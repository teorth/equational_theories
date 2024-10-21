import equational_theories.EquationalResult
import equational_theories.Equations.All

namespace Eq1117

def op (a b : ℤ) : ℤ := 2 * a - b / 2

@[equational_result]
theorem _root_.Equation1117_not_implies_Equation2441 : ∃ (G : Type) (_ : Magma G), Equation1117 G ∧ ¬ Equation2441 G := by
  use ℤ, ⟨op⟩
  constructor
  · intro x y z
    simp only [op]
    omega
  · simp only [not_forall, op]
    use 1
    decide

end Eq1117
