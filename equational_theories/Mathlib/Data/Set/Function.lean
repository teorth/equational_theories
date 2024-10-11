import Mathlib.Data.Set.Function

variable {α β : Type*} {f : α → β} {s₁ : Set α} {t₁ : Set β} {a : α} {b : β}

theorem Set.BijOn.insert (h₁ : BijOn f s₁ t₁) (h₂ : f a ∉ t₁) :
    BijOn f (insert a s₁) (insert (f a) t₁) := by
  have ha : a ∉ s₁ := fun x ↦ (h₂ (h₁.mapsTo x))
  rw [insert_eq, insert_eq]
  apply Set.BijOn.union
  · simp
  · exact h₁
  · simp [injOn_insert ha, h₁.injOn]
    intro x hx h
    exact h₂ (h ▸ h₁.mapsTo hx)

theorem Set.BijOn.sdiff_singleton (h₁ : BijOn f s₁ t₁) (h₂ : a ∈ s₁) :
    BijOn f (s₁ \ {a}) (t₁ \ {f a}) := by
  convert h₁.subset_left diff_subset
  simp only [h₁.injOn.image_diff, h₁.image_eq, singleton_subset_iff, h₂,
    inter_eq_self_of_subset_right, image_singleton]
