import Mathlib.Data.Set.Basic

variable {α : Type*} {s : Set α}

theorem Set.diff_insert_of_not_mem {x : α} (h : x ∉ s) (t : Set α) : s \ insert x t = s \ t := by
  refine Subset.antisymm (diff_subset_diff (Subset.refl _) (subset_insert _ _)) fun y hy => ?_
  simp only [mem_diff, mem_insert_iff, not_or] at hy ⊢
  exact ⟨hy.1, fun hxy => h <| hxy ▸ hy.1, hy.2⟩
