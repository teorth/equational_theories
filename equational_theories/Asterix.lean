import equational_theories.Equations
import equational_theories.Mathlib.Data.Set.Basic
import equational_theories.Mathlib.Data.Set.Function
import equational_theories.Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Logic.Equiv.Nat

-- equation 65 := x = y ◇ (x ◇ (y ◇ x))

namespace Asterix

variable {G : Type*} [DecidableEq G]

variable (G) in
@[ext]
structure PartialSolution where
  E0 : Finset (G × G)
  E1 : Finset (G × G)
  f : G → G → G
  E0_subset_E1 : E0 ⊆ E1
  t_mem_of_mem_E0' : ∀ x ∈ E0, (x.2, f x.1 x.2) ∈ E1
  mem_2_of_mem_E0 : ∀ x ∈ E0, (x.1, f x.2 (f x.1 x.2)) ∈ E1
  eq_of_mem_E0 : ∀ x ∈ E0, f x.1 (f x.2 (f x.1 x.2)) = x.2
  undef_of_not_mem_E0 : ∀ x ∈ E1 \ E0, (x.2, f x.1 x.2) ∉ E1

def PartialSolution.g (f : PartialSolution G) : G × G → G × G :=
  fun (x, y) => (y, f.f x y)

instance : Preorder (PartialSolution G) where
  le a b := a.E0 ≤ b.E0 ∧ a.E1 ≤ b.E1 ∧ Set.EqOn a.f.uncurry b.f.uncurry a.E1
  le_refl := by simp [Set.EqOn]
  le_trans a b c hab hbc := by aesop (add forward subset_trans safe) (add simp [Set.EqOn])

lemma le_def {a b : PartialSolution G} : a ≤ b ↔
  a.E0 ≤ b.E0 ∧ a.E1 ≤ b.E1 ∧ Set.EqOn a.f.uncurry b.f.uncurry a.E1 := Iff.rfl

lemma PartialSolution.t_mem_of_mem_E0 (f : PartialSolution G) (x : G × G) (hx : x ∈ f.E0) :
    f.g x ∈ f.E1 := f.t_mem_of_mem_E0' x hx

lemma PartialSolution.undef_of_not_mem_E1 (f : PartialSolution G) (x : G × G) (hx : x ∉ f.E0)
    (hx2 : x ∈ f.E1) : f.g x ∉ f.E1 := f.undef_of_not_mem_E0 x (by simp [*])

-- def move_e1_e0 (f : PartialSolution ℤ) (h0 h2 : ℤ × ℤ) (hE0 : h0 ∉ f.E0) (hE1 : h0 ∈ f.E1)
--     (hne1 : h2 ≠ -f.f h0 - h2) (hne2 : h0 + f.f h0 + h2 ≠ -f.f h0 - h2)
--     (hnotmem : h2 ∉ f.E2) (hnotmem2 : h0 + f.f h0 + h2 ∉ f.E2) (hnotmem3 : -f.f h0 - h2 ∉ f.E2) :
--     PartialSolution ℤ :=
--   let h1 := f.f h0
--   have h1_in_E2 : h1 ∈ f.E2 := f.maps_E1_E2 hE1
--   have h1_not_in_E1 : h1 ∉ f.E1 := (f.f_bijOn.mapsTo ⟨hE1, hE0⟩).2
--   have h0_ne_h1 : h0 ≠ h1 := fun h ↦ h1_not_in_E1 (h ▸ hE1)
--   have h0_ne_sum : h0 ≠ h0 + h1 + h2 := fun nh ↦ hnotmem2 (nh ▸ (f.E1_subset_E2 hE1))
--   have sum_ne_h1 : h0 + h1 + h2 ≠ h1 := fun nh ↦ hnotmem2 (nh ▸ h1_in_E2)

--   {
--   E0 := f.E0 ∪ {h0},
--   E1 := f.E1 ∪ {h1, h0 + h1 + h2},
--   E2 := f.E2 ∪ {h0 + h1 + h2, h2, -h1 -h2},
--   niceE2 := by rw [Set.image_union, Set.finite_union]; simp only [f.niceE2, Set.image_insert_eq,
--     Prod.fst_add, Set.image_singleton, Prod.fst_sub, Prod.fst_neg, Set.finite_singleton,
--     Set.Finite.insert, and_self]
--   f := fun x ↦ if x = h1 then h2 else if x = h0 + h1 + h2 then -h1 -h2
--         else f.f x
--   E0_subset_E1 := by intro a ha; aesop (add forward safe PartialSolution.E0_subset_E1)
--   E1_subset_E2 := by intro a ha; aesop (add forward safe PartialSolution.E1_subset_E2)
--   zero_mem_E0 := by simp [f.zero_mem_E0]
--   f_ne_neg := by
--     intro a ha
--     dsimp only
--     split
--     · subst a
--       rintro rfl
--       simp only [add_neg_cancel_right] at hnotmem2
--       exact hnotmem2 (f.E1_subset_E2 hE1)
--     split
--     · subst a
--       suffices h0 ≠ 0 by
--         rw [ne_eq, ← sub_eq_zero]
--         simpa [← sub_sub]
--       rintro rfl
--       simp at hE0
--     · apply f.f_ne_neg
--       simp_all only [ne_eq, Set.union_insert, Set.union_singleton, Set.mem_diff, Set.mem_insert_iff,
--         false_or, not_or, not_false_eq_true, and_self]
--   maps_E0_E1 := by
--     apply Set.MapsTo.union_union
--     · apply f.maps_E0_E1.congr
--       intro x hx
--       dsimp only
--       rw [if_neg, if_neg]
--       · rintro rfl
--         exact hnotmem2 (f.E0_subset_E2 hx)
--       · rintro rfl
--         exact h1_not_in_E1 (f.E0_subset_E1 hx)
--     · simp only [Finset.coe_singleton, Finset.coe_insert, Set.mapsTo_singleton, Set.mem_insert_iff,
--       Set.mem_singleton_iff]
--       rw [if_neg, if_neg]
--       · exact .inl rfl
--       · exact h0_ne_sum
--       · exact h0_ne_h1
--   maps_E1_E2 := by
--     apply Set.MapsTo.union_union
--     · apply f.maps_E1_E2.congr
--       intro x hx
--       dsimp only
--       rw [if_neg, if_neg]
--       · rintro rfl
--         exact hnotmem2 (f.E1_subset_E2 hx)
--       · rintro rfl
--         exact h1_not_in_E1 hx
--     · intro x hx
--       simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
--         Set.mem_singleton_iff] at hx
--       rcases hx with rfl | rfl
--       · simp
--       · simp only [Finset.coe_insert, Finset.coe_singleton, ↓reduceIte, Set.mem_insert_iff,
--         ite_eq_left_iff, Set.mem_singleton_iff, ite_eq_right_iff]
--         right; right
--         intro nh
--         exact (hnotmem2 (nh ▸ h1_in_E2)).elim
--   eq_f_mem_E1 := by
--     intro x hx
--     dsimp only
--     simp only [Set.mem_union, Set.mem_singleton] at hx
--     rcases hx with hx | hx
--     · have v1 : x ≠ h0 + h1 + h2 := fun nh ↦ hnotmem2 (f.E0_subset_E2 (nh ▸ hx))
--       have v2 : x ≠ h1 := fun nh ↦ h1_not_in_E1 (f.E0_subset_E1 (nh ▸ hx))
--       have v4 : f.f x ≠ h0 + h1 + h2 := fun nh ↦ hnotmem2 (nh ▸ f.maps_E0_E2 hx)
--       have v3 : f.f x ≠ h1 := fun nh ↦ h1_not_in_E1 (nh ▸ f.maps_E0_E1 hx)
--       simp [v1, v2, v3, v4, f.eq_f_mem_E1 x hx]
--     · subst x
--       simp only [Set.union_insert, h0_ne_h1, ↓reduceIte, h0_ne_sum, Set.mem_insert_iff,
--         Set.mem_union, Set.mem_singleton, or_true]
--   eq_f_eq_zero := by
--     intro x hx
--     dsimp only
--     simp only [Set.mem_union, Set.mem_singleton] at hx
--     rcases hx with hx | hx
--     · have v1 : x ≠ h0 + h1 + h2 := fun nh ↦ hnotmem2 (f.E0_subset_E2 (nh ▸ hx))
--       have v2 : x ≠ h1 := fun nh ↦ h1_not_in_E1 (f.E0_subset_E1 (nh ▸ hx))
--       have v4 : f.f x ≠ h0 + h1 + h2 := fun nh ↦ hnotmem2 (nh ▸ f.maps_E0_E2 hx)
--       have v3 : f.f x ≠ h1 := fun nh ↦ h1_not_in_E1 (nh ▸ f.maps_E0_E1 hx)
--       have v5 : x + f.f x + f.f (f.f x) ≠ h1 := fun nh ↦ h1_not_in_E1 (nh ▸ f.eq_f_mem_E1 x hx)
--       have v6 : x + f.f x + f.f (f.f x) ≠ h0 + h1 + h2 := fun nh ↦ hnotmem2 (f.E1_subset_E2 (nh ▸ f.eq_f_mem_E1 x hx))
--       simp [v1, v2, v3, v4, v5, v6, f.eq_f_eq_zero x hx]
--     · subst x
--       simp only [h0_ne_h1, ↓reduceIte, h0_ne_sum, sum_ne_h1, h1]
--       abel
--   f_bijOn := by
--     simp only [Set.union_insert, Set.union_singleton, Set.mem_insert_iff, true_or, or_true,
--       Set.insert_diff_of_mem]
--     rw [Set.insert_diff_of_not_mem, Set.insert_diff_of_not_mem,
--       Set.insert_diff_of_not_mem, Set.insert_diff_of_not_mem]
--     · suffices Set.BijOn (fun x ↦ if x = h1 then h2 else if x = h0 + h1 + h2 then -h1 - h2 else f.f x)
--           (insert (h0 + h1 + h2) (↑f.E1 \ insert h0 ↑f.E0)) (insert (-h1 - h2) (↑f.E2 \ insert h1 (insert (h0 + h1 + h2) ↑f.E1))) by
--         convert this.insert _
--         · simp
--         · simp [hne1, hnotmem]
--       suffices Set.BijOn (fun x ↦ if x = h1 then h2 else if x = h0 + h1 + h2 then -h1 - h2 else f.f x)
--           (↑f.E1 \ insert h0 ↑f.E0) (↑f.E2 \ insert h1 (insert (h0 + h1 + h2) ↑f.E1)) by
--         convert this.insert _ using 2
--         · simp [sum_ne_h1]
--         · simp [sum_ne_h1, hne1, hnotmem3]
--       rw [Set.insert_comm]
--       nth_rw 2 [Set.diff_insert_of_not_mem]
--       rw [Set.insert_eq, Set.insert_eq, Set.union_comm, ← Set.diff_diff, Set.union_comm, ← Set.diff_diff]
--       suffices Set.BijOn (fun x ↦ if x = h1 then h2 else if x = h0 + h1 + h2 then -h1 - h2 else f.f x)
--           (↑f.E1 \ ↑f.E0) (↑f.E2 \ ↑f.E1) by
--         convert this.sdiff_singleton (a := h0) _
--         · simp [h0_ne_h1, h0_ne_sum]
--         · simp [hE0, hE1]
--       apply f.f_bijOn.congr
--       intro x hx
--       aesop (add forward safe PartialSolution.E1_subset_E2)
--       exact hnotmem2
--     · simp only [Set.mem_insert_iff, hne2.symm, Finset.mem_coe, false_or, not_or]
--       exact ⟨fun nh ↦ hnotmem3 (nh ▸ h1_in_E2), fun nh ↦ hnotmem3 (f.E1_subset_E2 nh)⟩
--     · simp only [Set.mem_insert_iff, self_eq_add_left, Finset.mem_coe, not_or]
--       split_ands
--       · rintro rfl
--         contradiction
--       · exact f.add_ne_zero _ hE1 hE0
--       · exact fun nh ↦ hnotmem (f.E1_subset_E2 nh)
--     · simp only [Set.mem_insert_iff, h0_ne_sum.symm, Finset.mem_coe, false_or]
--       exact fun nh ↦ hnotmem2 (f.E0_subset_E2 nh)
--     · simp only [Set.mem_insert_iff, h0_ne_h1.symm, Finset.mem_coe, false_or]
--       exact fun nh ↦ h1_not_in_E1 (f.E0_subset_E1 nh)
--   }

-- lemma le_move_e1_e0 (f : PartialSolution ℤ) (h0 h2 : ℤ × ℤ) (hE0 : h0 ∉ f.E0) (hE1 : h0 ∈ f.E1)
--     (hne1 : h2 ≠ -f.f h0 - h2) (hne2 : h0 + f.f h0 + h2 ≠ -f.f h0 - h2)
--     (hnotmem : h2 ∉ f.E2) (hnotmem2 : h0 + f.f h0 + h2 ∉ f.E2) (hnotmem3 : -f.f h0 - h2 ∉ f.E2) :
--     f ≤ move_e1_e0 f h0 h2 hE0 hE1 hne1 hne2 hnotmem hnotmem2 hnotmem3 := by
--   simp only [move_e1_e0, Set.union_singleton, Set.union_insert, le_def, Set.le_eq_subset,
--     Set.subset_insert, true_and]
--   simp_all only [ne_eq, Set.subset_def, Set.mem_union, Set.mem_singleton, true_or, implies_true,
--     Set.mem_insert_iff, or_true, true_and]
--   intro x hx
--   dsimp only
--   rw [if_neg, if_neg]
--   · intro nh
--     exact hnotmem2 (f.E1_subset_E2 (nh ▸ hx))
--   · rintro rfl
--     exact (f.f_bijOn.mapsTo ⟨hE1, hE0⟩).2 hx

-- def add_e1 (f : PartialSolution ℤ) (h0 h1 : ℤ × ℤ) (hh0 : h0 ∉ f.E2) (hh1 : h1 ∉ f.E2)
--     (hne : h0 ≠ h1) (hadd : h0 + h1 ≠ 0) : PartialSolution ℤ where
--   E0 := f.E0
--   E1 := f.E1 ∪ {h0}
--   E2 := f.E2 ∪ {h0, h1}
--   niceE2 := by rw [Set.image_union, Set.finite_union]; simp only [f.niceE2, Set.image_insert_eq,
--     Prod.fst_add, Set.image_singleton, Prod.fst_sub, Prod.fst_neg, Set.finite_singleton,
--     Set.Finite.insert, and_self]
--   f := fun x ↦ if x = h0 then h1 else f.f x
--   E0_subset_E1 := by intro; aesop (add forward safe PartialSolution.E0_subset_E1)
--   E1_subset_E2 := by intro; aesop (add forward safe PartialSolution.E1_subset_E2)
--   zero_mem_E0 := by simp [f.zero_mem_E0]
--   f_ne_neg := by
--     intro x hx
--     dsimp only
--     split
--     · subst x
--       simp only [ne_eq, ← add_eq_zero_iff_eq_neg', hadd, not_false_eq_true]
--     · apply f.f_ne_neg
--       aesop
--   maps_E0_E1 := by
--     apply Set.MapsTo.mono_right _ (Set.subset_union_left)
--     apply f.maps_E0_E1.congr
--     intro x hx
--     aesop (add forward safe [PartialSolution.E0_subset_E2])
--   maps_E1_E2 := by
--     apply Set.MapsTo.union_union
--     · apply f.maps_E1_E2.congr
--       intro x hx
--       aesop (add forward safe PartialSolution.E1_subset_E2)
--     · intro x hx
--       aesop
--   eq_f_mem_E1 := by
--     intro h hh
--     dsimp only
--     rw [if_neg, if_neg]
--     · simp [f.eq_f_mem_E1 h hh]
--     · have := f.maps_E0_E1 hh
--       simp_all only [ne_eq, Finset.mem_coe]
--       intro a
--       subst a
--       exact hh0 (f.E1_subset_E2 this)
--     · simp_all only [ne_eq]
--       intro a
--       subst a
--       exact hh0 (f.E0_subset_E2 hh)
--   eq_f_eq_zero := by
--     intro h hh
--     dsimp only
--     rw [if_neg, if_neg, if_neg]
--     · simp [f.eq_f_eq_zero h hh]
--     · intro nh
--       subst nh
--       exact hh0 (f.E1_subset_E2 (f.eq_f_mem_E1 h hh))
--     · simp_all only [ne_eq, Finset.mem_coe]
--       intro a
--       subst a
--       exact hh0 (f.maps_E0_E2 hh)
--     · simp_all only [ne_eq]
--       intro a
--       subst a
--       exact hh0 (f.E0_subset_E2 hh)
--   f_bijOn := by
--     simp only [Set.union_singleton, Set.union_insert, Set.mem_insert_iff, true_or,
--       Set.insert_diff_of_mem]
--     rw [Set.insert_diff_of_not_mem, Set.insert_diff_of_not_mem, Set.diff_insert_of_not_mem]
--     · suffices Set.BijOn (fun x ↦ if x = h0 then h1 else f.f x) (↑f.E1 \ ↑f.E0) (↑f.E2 \ ↑f.E1) by
--         convert this.insert _
--         · simp
--         · simp [hh1]
--       apply f.f_bijOn.congr
--       intro x hx
--       aesop (add forward safe PartialSolution.E1_subset_E2)
--     · exact hh0
--     · simp [hne.symm]
--       exact hh1 ∘ (f.E1_subset_E2 ·)
--     · exact hh0 ∘ (f.E0_subset_E2 ·)

-- lemma le_add_e1 (f : PartialSolution ℤ) (h0 h1 : ℤ × ℤ) (hh0 : h0 ∉ f.E2) (hh1 : h1 ∉ f.E2)
--     (hne : h0 ≠ h1) (hadd : h0 + h1 ≠ 0) :
--     f ≤ add_e1 f h0 h1 hh0 hh1 hne hadd := by
--   simp [add_e1, le_def]
--   simp_all only [ne_eq, Set.subset_def, Set.mem_union, Set.mem_singleton, true_or,
--     implies_true, Set.mem_insert_iff, or_true, true_and]
--   intro x hx
--   dsimp only
--   rw [if_neg]
--   rintro rfl
--   exact hh0 (f.E1_subset_E2 hx)

-- open Pointwise

-- private theorem exists_nice_triple (S : Set (ℤ × ℤ)) (hS : (Prod.fst '' S).Finite) (h0 h1 : ℤ × ℤ) :
--   ∃ h2, h2 ≠ -h1 -h2 ∧ h0 + h1 + h2 ≠ -h1 -h2 ∧
--     h2 ∉ S ∧ h0 + h1 + h2 ∉ S ∧ -h1 -h2 ∉ S := by
--   sorry
--   -- obtain ⟨h2, hh2⟩ := Infinite.exists_not_mem_finset (S ∪ {-h1/2, -h0/2-h1} ∪ (-h1 +ᵥ -S) ∪ ((-h0 + -h1) +ᵥ S))
--   -- use h2
--   -- simp only [Finset.union_assoc, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_vadd_finset,
--   --   Finset.mem_neg', vadd_eq_add, not_or, not_exists, not_and] at hh2
--   -- split_ands
--   -- · omega
--   -- · omega
--   -- · exact hh2.1
--   -- · intro nh
--   --   replace hh2 := hh2.2.2.2 (h0 + h1 + h2) nh
--   --   omega
--   -- · intro nh
--   --   replace hh2 := hh2.2.2.1 (h1 + h2) (by simpa [add_comm])
--   --   omega

-- theorem lemma720 (f : PartialSolution ℤ) (h0 : ℤ × ℤ) (hh : h0 ∈ f.E0) :
--     ∃ g ≥ f, h0 ∈ g.E0 := by use f

-- theorem lemma721 (f : PartialSolution ℤ) (h0 : ℤ × ℤ) (hh : h0 ∈ f.E1) (hnh : h0 ∉ f.E0) :
--     ∃ g ≥ f, h0 ∈ g.E0 := by
--   obtain ⟨h2, ne1, ne2, m1, m2, m3⟩ := exists_nice_triple f.E2 f.niceE2 h0 (f.f h0)
--   use move_e1_e0 f h0 h2 hnh hh ne1 ne2 m1 m2 m3, le_move_e1_e0 ..
--   simp [move_e1_e0]


-- theorem lemma722 (f : PartialSolution ℤ) (h0 : ℤ × ℤ) (hnh : h0 ∉ f.E2) :
--     ∃ g ≥ f, h0 ∈ g.E0 := by
--   obtain ⟨h1, hh1⟩ : ∃ x, x ∉ (f.E2 ∪ {h0, -h0}) := sorry
--   simp only [Set.union_insert, Set.union_singleton, Set.mem_insert_iff, not_or] at hh1
--   let f' := add_e1 f h0 h1 hnh hh1.2.2 (Ne.symm hh1.1) (by simp [add_eq_zero_iff_eq_neg', hh1])
--   obtain ⟨g, hg1, hg2⟩ := lemma721 f' h0 (by simp [f', add_e1])
--     (by simp only [add_e1, Finset.union_insert, f']; intro nh; exact hnh (f.E0_subset_E2 nh))
--   use g, (le_add_e1 ..).trans hg1, hg2

-- theorem lemma723 (f : PartialSolution ℤ) (h0 : ℤ × ℤ) (hh : h0 ∈ f.E2) (hnh : h0 ∉ f.E1) :
--     ∃ g ≥ f, h0 ∈ g.E0 := by
--   obtain ⟨x', hx'1, hx'2⟩ := f.f_bijOn.surjOn ⟨hh, hnh⟩
--   obtain ⟨f', hf'1, hf'2⟩ := lemma721 f x' hx'1.1 hx'1.2
--   replace hx'2 : f'.f x' = h0 := by
--     subst hx'2
--     apply hf'1.2.2.2.symm
--     exact hx'1.1
--   by_cases hh0 : h0 ∈ f'.E0
--   · use f'
--   obtain ⟨g, hg1, hg2⟩ := lemma721 f' h0 (hx'2 ▸ f'.maps_E0_E1 hf'2) hh0
--   use g, hf'1.trans hg1, hg2

-- theorem lemma72 (f : PartialSolution ℤ) (h0 : ℤ × ℤ) :
--     ∃ g ≥ f, h0 ∈ g.E0 := by
--   by_cases hE2 : h0 ∉ f.E2
--   · apply lemma722 _ _ hE2
--   by_cases hE1 : h0 ∉ f.E1
--   · apply lemma723 <;> simp_all
--   by_cases hE0 : h0 ∉ f.E0
--   · apply lemma721 <;> simp_all
--   · apply lemma720
--     simp_all

-- def Equiv.pairIntNat : (ℤ × ℤ) ≃ ℕ :=
--   (Equiv.prodCongr Equiv.intEquivNat Equiv.intEquivNat).trans Nat.pairEquiv


-- noncomputable def closureSeq (f : PartialSolution ℤ) : ℕ → PartialSolution ℤ
-- | 0 => f
-- | n+1 => (lemma72 (closureSeq f n) (Equiv.pairIntNat.symm n)).choose

-- lemma closureSeq_le_closureSeq_succ (f : PartialSolution ℤ) (n : ℕ) :
--     closureSeq f n ≤ closureSeq f (n + 1) :=
--   (Exists.choose_spec <| lemma72 (closureSeq f n) (Equiv.pairIntNat.symm n)).1

-- lemma mem_closureSeq_e0 (f : PartialSolution ℤ) (n : ℤ × ℤ) :
--     n ∈ (closureSeq f (Equiv.pairIntNat n + 1)).E0 := by
--   simp only [closureSeq, ge_iff_le, Equiv.symm_apply_apply]
--   generalize_proofs pf
--   exact pf.choose_spec.2

-- lemma closureSeq_mono (f : PartialSolution ℤ) : Monotone (closureSeq f) := by
--   intro n m hnm
--   obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hnm
--   clear hnm
--   induction m
--   case zero => simp
--   case succ m hm =>
--     apply hm.trans
--     rw [← add_assoc]
--     apply closureSeq_le_closureSeq_succ

-- lemma le_closureSeq (f : PartialSolution ℤ) (n : ℕ) :f ≤ closureSeq f n :=
--   closureSeq_mono f (Nat.zero_le n)

-- noncomputable def closure (f : PartialSolution ℤ) : ℤ × ℤ → ℤ × ℤ :=
--   fun n ↦ (closureSeq f (Equiv.pairIntNat n + 1)).f n

-- lemma closure_eq_of_mem_e1 (f : PartialSolution ℤ) (n : ℕ) (x : ℤ × ℤ) (hn : x ∈ (closureSeq f n).E1) :
--     closure f x = (closureSeq f n).f x := by
--   simp [closure]
--   rcases le_total n (Equiv.pairIntNat x + 1) with h | h
--   · apply (closureSeq_mono f h).2.2.2.symm
--     apply hn
--   · apply (closureSeq_mono f h).2.2.2
--     apply PartialSolution.E0_subset_E1
--     exact mem_closureSeq_e0 f x

-- lemma lemma73 (f : PartialSolution ℤ) :
--     ∃ g : ℤ × ℤ → ℤ × ℤ, Set.EqOn g f.f f.E1 ∧ ∀ h, g h + g (g h) + g (h + g h + g (g h)) = 0 := by
--   use closure f
--   constructor
--   · intro x hx
--     rw [closure, eq_comm]
--     apply (le_closureSeq f (Equiv.pairIntNat x + 1)).2.2.2 hx
--   · intro x
--     rw [closure_eq_of_mem_e1 f (Equiv.pairIntNat x + 1), closure_eq_of_mem_e1 f (Equiv.pairIntNat x + 1),
--       closure_eq_of_mem_e1 f (Equiv.pairIntNat x + 1)]
--     · apply (closureSeq f (Equiv.pairIntNat x + 1)).eq_f_eq_zero
--       apply mem_closureSeq_e0
--     · apply (closureSeq f (Equiv.pairIntNat x + 1)).eq_f_mem_E1
--       apply mem_closureSeq_e0
--     · apply (closureSeq f (Equiv.pairIntNat x + 1)).maps_E0_E1
--       apply mem_closureSeq_e0
--     · apply (closureSeq f (Equiv.pairIntNat x + 1)).E0_subset_E1
--       apply mem_closureSeq_e0

-- def initial : PartialSolution ℤ where
--   E0 := (fun n ↦ (0, n)) '' {n | -1 ≤ n}
--   E1 := (fun n ↦ (0, n)) '' {n | -1 ≤ n}
--   E2 := (fun n ↦ (0, n)) '' {n | -1 ≤ n}
--   niceE2 := by
--     simp only [Int.reduceNeg, Set.image_image]
--     rw [Set.Nonempty.image_const]
--     · simp only [Set.finite_singleton]
--     use 0
--     decide
--   f := fun n ↦ if 0 ≤ n.snd then (0, -1) else (0, 2)
--   E0_subset_E1 := by simp
--   E1_subset_E2 := by simp
--   zero_mem_E0 := by simp
--   f_ne_neg := by simp
--   maps_E0_E1 := by
--     intro x _
--     dsimp only
--     split <;> simp
--   maps_E1_E2 := by
--     intro x _
--     dsimp only
--     split <;> simp
--   eq_f_mem_E1 := by
--     simp only [Int.reduceNeg, Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp,
--       forall_apply_eq_imp_iff₂]
--     intro a ha
--     split
--     · simp only [Int.reduceNeg, Prod.mk_add_mk, add_zero, Left.nonneg_neg_iff, Int.reduceLE,
--       ↓reduceIte, Prod.mk.injEq, true_and, exists_eq_right]
--       omega
--     · simp only [Int.reduceNeg, Prod.mk_add_mk, add_zero, Nat.ofNat_nonneg, ↓reduceIte,
--       Prod.mk.injEq, true_and, exists_eq_right, le_add_iff_nonneg_left]
--       omega
--   eq_f_eq_zero := by
--     simp only [Int.reduceNeg, Set.mem_image, Set.mem_setOf_eq, Prod.snd_add, forall_exists_index,
--       and_imp, forall_apply_eq_imp_iff₂]
--     intro a ha
--     split
--     · simp only [Int.reduceNeg, Left.nonneg_neg_iff, Int.reduceLE, ↓reduceIte, Prod.mk_add_mk,
--       add_zero, Int.reduceAdd]
--       rw [if_pos]
--       rfl
--       omega
--     · simp only [Nat.ofNat_nonneg, ↓reduceIte, Int.reduceNeg, Prod.mk_add_mk, add_zero,
--       Int.reduceAdd, le_add_neg_iff_add_le, zero_add]
--       rw [if_pos]
--       rfl
--       omega
--   f_bijOn := by simp

-- -- h0 h1 h2: 1, 4, 5. h0' h1' h2': 2, 3, 7
-- -- def initial : PartialSolution ℤ where
-- --   E0 := {0, 1, 2}
-- --   E1 := {0, 1, 2, 3, 4, 10, 12}
-- --   E2 := {0, 1, 2, 3, 4, 5, 7, 10, 12, -9, -10} -- note, add h2 to blueprint
-- --   E0_subset_E1 := by decide
-- --   E1_subset_E2 := by decide
-- --   f x := if x = 1 then 4 else if x = 2 then 3 else if x = 3 then 7 else if
-- --     x = 4 then 5 else if x = 10 then -9 else if x = 12 then -10 else 0
-- --   zero_mem_E0 := by decide
-- --   f_ne_neg := by decide
-- --   eq_f_mem_E1 := by decide
-- --   eq_f_eq_zero := by decide
-- --   maps_E0_E1 := by decide
-- --   maps_E1_E2 := by decide
-- --   f_bijOn := by rw [← Finset.coe_sdiff, ← Finset.coe_sdiff]; decide

-- noncomputable def closure_initial : ℤ × ℤ → ℤ × ℤ := (lemma73 initial).choose

-- lemma closure_initial_prop1 : ∀ h,
--     closure_initial h + closure_initial (closure_initial h) +
--       closure_initial (h + closure_initial h + closure_initial (closure_initial h)) = 0 :=
--   (lemma73 initial).choose_spec.2

-- lemma closure_initial_prop2 :
--     ∀ x ∈ initial.E1, closure_initial x = initial.f x := (lemma73 initial).choose_spec.1

-- -- lemma closure_initial_one : closure_initial (0, 0) = (0, -1) := closure_initial_prop2 (0, 0) (by simp [initial])

-- lemma closure_initial_zero : closure_initial 0 = (0, -1) := closure_initial_prop2 0 (by simp [initial])

-- lemma closure_initial_zero_one : closure_initial (0, 1) = (0, -1) := closure_initial_prop2 (0, 1) (by simp [initial])

-- -- lemma closure_initial_two : closure_initial 2 = 3 := closure_initial_prop2 2 (by decide)

-- theorem Equation65_not_implies_Equation359 : ∃ (G: Type) (_: Magma G), Equation65 G ∧ ¬ Equation359 G := by
--   use ℤ × ℤ, translationInvariant closure_initial, ?_, ?_
--   rw [Equation65_translationInvariant_iff]
--   apply closure_initial_prop1
--   intro nh
--   have v1 := nh (1, 1)
--   simp only [translationInvariant, Prod.mk_zero_zero, sub_self, closure_initial_zero, Int.reduceNeg,
--     zero_add, zero_sub, Prod.neg_mk, neg_zero, neg_neg, closure_initial_zero_one] at v1
--   have v2 := nh 2 0
--   simp [translationInvariant, closure_initial_two] at v2
--   omega

-- -- @[equational_result]
-- -- theorem Equation65_not_implies_Equation1491 : ∃ (G: Type) (_: Magma G), Equation65 G ∧ ¬ Equation1491 G := by
-- --   use ℤ, translationInvariant closure_initial, ?_, ?_
-- --   rw [Equation65_translationInvariant_iff]
-- --   apply closure_initial_prop1
-- --   intro nh
-- --   have v1 := nh 1 0
-- --   simp [translationInvariant, closure_initial_one] at v1
-- --   have v2 := nh 2 0
-- --   simp [translationInvariant, closure_initial_two] at v2
-- --   omega
