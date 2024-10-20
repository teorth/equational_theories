import equational_theories.EquationalResult
import equational_theories.Equations.All
import equational_theories.FactsSyntax

namespace Eq3342

def op (a b : Option (ℕ × ℕ)) : Option (ℕ × ℕ) :=
  match a, b with
  | some (a, b),  some (c, d) =>
    if b = d ∧ (a = c ∨ a + 1 = c) then (0, b + 1) else
    if b + 1 = d ∧ a ≥ c then (a-c+1, b) else
    if b = d + 1 ∧ a < c then (c-a, d) else
    none
  | none, _ => none
  | _, none => none

theorem Equation3342_facts : ∃ (G : Type) (_ : Magma G), Facts G [3342] [3456, 3522, 4065, 4118] := by
  use Option (ℕ × ℕ), ⟨op⟩
  split_ands
  · intro x y
    cases x
    cases y
    · rfl
    · rfl
    cases y
    · simp [op]
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

end Eq3342
