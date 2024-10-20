import Mathlib.Data.Set.Function

variable {α β : Type*} {f : α → β} {s₁ : Set α} {t₁ : Set β} {a : α} {b : β}

-- Mathlib PR: https://github.com/leanprover-community/mathlib4/pull/17971
theorem Set.BijOn.insert (h₁ : BijOn f s₁ t₁) (h₂ : f a ∉ t₁) :
    BijOn f (insert a s₁) (insert (f a) t₁) := by
  repeat rw [insert_eq]
  refine Set.BijOn.union (bijOn_singleton.mpr rfl) h₁ ?_
  simp [injOn_insert fun x ↦ (h₂ (h₁.mapsTo x)), h₁.injOn]
  exact fun _ hx h ↦ h₂ (h ▸ h₁.mapsTo hx)

-- Mathlib PR: https://github.com/leanprover-community/mathlib4/pull/17971
theorem Set.BijOn.sdiff_singleton (h₁ : BijOn f s₁ t₁) (h₂ : a ∈ s₁) :
    BijOn f (s₁ \ {a}) (t₁ \ {f a}) := by
  convert h₁.subset_left diff_subset
  simp [h₁.injOn.image_diff, h₁.image_eq, h₂, inter_eq_self_of_subset_right]
