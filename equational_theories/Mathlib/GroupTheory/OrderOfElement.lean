import Mathlib.GroupTheory.OrderOfElement

universe u

variable {α : Type u}

theorem isOfFinOrder_of_isConj [Group α] {x y : α} :
      IsConj x y → (IsOfFinOrder x → IsOfFinOrder y) := by
   simp only [isConj_iff, isOfFinOrder_iff_pow_eq_one]
   refine fun ⟨u, eq⟩ ⟨n, n_gt_0, eq'⟩ ↦ ⟨n, n_gt_0, ?_⟩
   rw [← eq, conj_pow, eq', mul_one, mul_inv_cancel]
