import Mathlib.Data.Set.Finite.Basic
import equational_theories.Equations.All

@[equational_result]
theorem Equation677_and_8_implies_Equation255 (G : Type _) [Magma G] [Finite G]
    (h : Equation677 G) (h2 : Equation8 G) : Equation255 G := by
  change ∀ _, _ at h h2 ⊢
  intro x
  have h_surj (y : G) : Set.SurjOn (fun s ↦ y ◇ s) Set.univ Set.univ := by
    intro s
    simp
    use (s ◇ ((y ◇ s) ◇ y))
    rw [← h]
  conv at h_surj =>
    enter [y]
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) (by simp)]
  replace h_surj (y) := (h_surj y).injOn
  have h3 (y) := (h2 y).symm.trans (h y y)
  replace h3 (y) := h_surj y (by trivial) (by trivial) (h3 y)
  replace h3 (y) := h_surj y (by trivial) (by trivial) (h3 y)
  specialize h2 x
  specialize h x (x ◇ x)
  simp only [← h3, ← h2] at h
  specialize h3 (x ◇ x)
  rw [← h, ← h2] at h3
  simp only [h3]

/-
Prints:
`Equation677_and_8_implies_Equation255: Equation677&Equation8 → Equation255`
since at this point in the imports this is the only implication in the records.
-/
#print_equational_results multi
