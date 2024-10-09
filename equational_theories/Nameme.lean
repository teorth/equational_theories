import equational_theories.AllEquations
import equational_theories.EquationalResult
import Mathlib.Tactic.FinCases

@[equational_result]
theorem Equation359_not_implies_Equation65 : ∃ (G: Type) (_: Magma G), Equation359 G ∧ ¬ Equation65 G := by
  use Fin 2, ⟨fun a b ↦ a * b⟩
  constructor
  · intro x
    fin_cases x <;> decide
  · unfold Equation65
    push_neg
    use 1, 0
    decide
