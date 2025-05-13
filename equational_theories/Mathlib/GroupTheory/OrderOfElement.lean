import Mathlib.GroupTheory.OrderOfElement

universe u

variable {α : Type u}

theorem isOfFinOrder_of_isConj [Group α] {x y : α} :
      IsConj x y → (IsOfFinOrder x → IsOfFinOrder y) := by
   simp only [isConj_iff]
   repeat rw [isOfFinOrder_iff_pow_eq_one]
   intro ⟨u, eq⟩ ⟨n, n_gt_0, eq'⟩
   use n, n_gt_0
   rw [← eq]
   simp only [conj_pow, conj_eq_one_iff, eq']
