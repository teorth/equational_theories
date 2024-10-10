import equational_theories.Equations
import equational_theories.Mathlib.Data.Set.Basic
import equational_theories.Mathlib.Data.Set.Function
import Mathlib.Tactic.Abel
import Mathlib.Data.Fintype.Card

-- equation 65 := x = y ◇ (x ◇ (y ◇ x))

section AddCommGroup

variable {G : Type*} [AddCommGroup G]

def translationInvariant (f : G → G) : Magma G where
  op y x := x + f (x - y)

lemma Equation65_translationInvariant_iff (f : G → G) :
  @Equation65 G (translationInvariant f) ↔ ∀ h, f h + f (f h) + f (h + f h + f (f h)) = 0 := by
  simp [Equation65, Magma.op, translationInvariant]
  constructor
  · intro hxy h
    rw [hxy 0 (-h)]
    simp [← add_rotate]
  · intro hh x y
    conv =>
      enter [2, 2, 1]
      rw [add_rotate, add_sub_assoc, ← add_rotate]
    generalize x - y = h
    rw [add_assoc, add_assoc, eq_comm, ← sub_eq_zero, add_sub_cancel_left, ← add_assoc]
    apply hh

variable [DecidableEq G]

variable (G) in
@[ext]
structure PartialSolution where
  E0 : Finset G
  E1 : Finset G
  E2 : Finset G
  f : G → G
  E0_subset_E1 : E0 ⊆ E1
  E1_subset_E2 : E1 ⊆ E2
  zero_mem_E0 : 0 ∈ E0
  f_ne_neg : ∀ x ∈ E1 \ E0, f x ≠ -x
  maps_E0_E1 : Set.MapsTo f E0 E1
  maps_E1_E2 : Set.MapsTo f E1 E2
  eq_f_mem_E1 : ∀ h ∈ E0, h + f h + f (f h) ∈ E1
  eq_f_eq_zero : ∀ h ∈ E0, f h + f (f h) + f (h + f h + f (f h)) = 0
  f_bijOn : Set.BijOn f (E1 \ E0) (E2 \ E1)

instance : Preorder (PartialSolution G) where
  le a b := a.E0 ≤ b.E0 ∧ a.E1 ≤ b.E1 ∧ a.E2 ≤ b.E2 ∧ Set.EqOn a.f b.f a.E0
  le_refl := by simp [Set.EqOn]
  le_trans a b c hab hbc := by aesop (add forward subset_trans safe) (add simp [Set.EqOn])

lemma le_def {a b : PartialSolution G} : a ≤ b ↔
  a.E0 ≤ b.E0 ∧ a.E1 ≤ b.E1 ∧ a.E2 ≤ b.E2 ∧ Set.EqOn a.f b.f a.E0 := Iff.rfl

lemma PartialSolution.E0_subset_E2 (a : PartialSolution G) :
    a.E0 ⊆ a.E2 := a.E0_subset_E1.trans a.E1_subset_E2

lemma PartialSolution.maps_E0_E2 (a : PartialSolution G) :
    Set.MapsTo a.f a.E0 a.E2 := a.maps_E0_E1.mono_right (a.E1_subset_E2)

@[simp]
lemma zero_mem_E0 (a : PartialSolution G) : 0 ∈ a.E0 := a.zero_mem_E0

@[simp]
lemma zero_mem_E2 (a : PartialSolution G) : 0 ∈ a.E2 := by
  apply a.E0_subset_E2
  exact a.zero_mem_E0

end AddCommGroup

private theorem exists_nice_triple (S : Finset ℤ) (h0 h1 : ℤ) (hh : h0 + h1 ≠ 0) :
  ∃ h2, h2 ≠ -h1 -h2 ∧ h0 + h1 + h2 ≠ -h1 -h2 ∧
    h2 ∉ S ∧ h0 + h1 + h2 ∉ S ∧ -h1 -h2 ∉ S := by
  sorry

def move_e1_e0 (f : PartialSolution ℤ) (h0 h2 : ℤ) (hE0 : h0 ∉ f.E0) (hE1 : h0 ∈ f.E1)
    (hne1 : h2 ≠ -f.f h0 - h2) (hne2 : h0 + f.f h0 + h2 ≠ -f.f h0 - h2)
    (hnotmem : h2 ∉ f.E2) (hnotmem2 : h0 + f.f h0 + h2 ∉ f.E2) (hnotmem3 : -f.f h0 - h2 ∉ f.E2) :
    PartialSolution ℤ :=
  let h1 := f.f h0
  have h1_in_E2 : h1 ∈ f.E2 := f.maps_E1_E2 hE1
  have h1_not_in_E1 : h1 ∉ f.E1 := (f.f_bijOn.mapsTo ⟨hE1, hE0⟩).2
  have h0_ne_h1 : h0 ≠ h1 := fun h ↦ h1_not_in_E1 (h ▸ hE1)
  have h0_ne_sum : h0 ≠ h0 + h1 + h2 := fun nh ↦ hnotmem2 (nh ▸ (f.E1_subset_E2 hE1))
  have sum_ne_h1 : h0 + h1 + h2 ≠ h1 := fun nh ↦ hnotmem2 (nh ▸ h1_in_E2)

  {
  E0 := f.E0 ∪ {h0},
  E1 := f.E1 ∪ {h1, h0 + h1 + h2},
  E2 := f.E2 ∪ {h0 + h1 + h2, h2, -h1 -h2},
  f := fun x ↦ if x = h1 then h2 else if x = h0 + h1 + h2 then -h1 -h2
        else f.f x
  E0_subset_E1 := by intro a ha; aesop (add forward safe PartialSolution.E0_subset_E1)
  E1_subset_E2 := by intro a ha; aesop (add forward safe PartialSolution.E1_subset_E2)
  zero_mem_E0 := by simp [f.zero_mem_E0]
  f_ne_neg := by
    intro a ha
    dsimp only
    split
    · subst a
      rintro rfl
      simp only [add_neg_cancel_right] at hnotmem2
      exact hnotmem2 (f.E1_subset_E2 hE1)
    split
    · subst a
      suffices h0 ≠ 0 by omega
      rintro rfl
      simp at hE0
    · apply f.f_ne_neg
      simp_all only [ne_eq, Finset.union_insert, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union,
        Finset.mem_singleton, or_false, false_or, not_or, not_false_eq_true, and_self, h1]
  maps_E0_E1 := by
    simp only [Finset.coe_union]
    apply Set.MapsTo.union_union
    · apply f.maps_E0_E1.congr
      intro x hx
      dsimp only
      rw [if_neg, if_neg]
      · rintro rfl
        exact hnotmem2 (f.E0_subset_E2 hx)
      · rintro rfl
        exact h1_not_in_E1 (f.E0_subset_E1 hx)
    · simp only [Finset.coe_singleton, Finset.coe_insert, Set.mapsTo_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
      rw [if_neg, if_neg]
      · exact .inl rfl
      · exact h0_ne_sum
      · exact h0_ne_h1
  maps_E1_E2 := by
    simp only [Finset.coe_union]
    apply Set.MapsTo.union_union
    · apply f.maps_E1_E2.congr
      intro x hx
      dsimp only
      rw [if_neg, if_neg]
      · rintro rfl
        exact hnotmem2 (f.E1_subset_E2 hx)
      · rintro rfl
        exact h1_not_in_E1 hx
    · intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · simp
      · simp only [Finset.coe_insert, Finset.coe_singleton, ↓reduceIte, Set.mem_insert_iff,
        ite_eq_left_iff, Set.mem_singleton_iff, ite_eq_right_iff]
        right; right
        intro nh
        exact (hnotmem2 (nh ▸ h1_in_E2)).elim
  eq_f_mem_E1 := by
    intro x hx
    dsimp only
    simp only [Finset.mem_union, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · have v1 : x ≠ h0 + h1 + h2 := fun nh ↦ hnotmem2 (f.E0_subset_E2 (nh ▸ hx))
      have v2 : x ≠ h1 := fun nh ↦ h1_not_in_E1 (f.E0_subset_E1 (nh ▸ hx))
      have v4 : f.f x ≠ h0 + h1 + h2 := fun nh ↦ hnotmem2 (nh ▸ f.maps_E0_E2 hx)
      have v3 : f.f x ≠ h1 := fun nh ↦ h1_not_in_E1 (nh ▸ f.maps_E0_E1 hx)
      simp [v1, v2, v3, v4, f.eq_f_mem_E1 x hx]
    · subst x
      simp only [Finset.union_insert, h0_ne_h1, ↓reduceIte, h0_ne_sum, Finset.mem_insert,
        Finset.mem_union, Finset.mem_singleton, or_true]
  eq_f_eq_zero := by
    intro x hx
    dsimp only
    simp only [Finset.mem_union, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · have v1 : x ≠ h0 + h1 + h2 := fun nh ↦ hnotmem2 (f.E0_subset_E2 (nh ▸ hx))
      have v2 : x ≠ h1 := fun nh ↦ h1_not_in_E1 (f.E0_subset_E1 (nh ▸ hx))
      have v4 : f.f x ≠ h0 + h1 + h2 := fun nh ↦ hnotmem2 (nh ▸ f.maps_E0_E2 hx)
      have v3 : f.f x ≠ h1 := fun nh ↦ h1_not_in_E1 (nh ▸ f.maps_E0_E1 hx)
      have v5 : x + f.f x + f.f (f.f x) ≠ h1 := sorry
      have v6 : x + f.f x + f.f (f.f x) ≠ h0 + h1 + h2 := sorry
      simp [v1, v2, v3, v4, v5, v6, f.eq_f_eq_zero x hx]
    · subst x
      simp only [h0_ne_h1, ↓reduceIte, h0_ne_sum, sum_ne_h1, h1]
      omega
  f_bijOn := by
    simp only [Finset.union_insert, Finset.coe_insert, Finset.coe_union, Finset.coe_singleton,
      Set.union_singleton, Set.mem_insert_iff, Finset.mem_coe, true_or, or_true,
      Set.insert_diff_of_mem]
    rw [Set.insert_diff_of_not_mem, Set.insert_diff_of_not_mem,
      Set.insert_diff_of_not_mem, Set.insert_diff_of_not_mem]
    · suffices Set.BijOn (fun x ↦ if x = h1 then h2 else if x = h0 + h1 + h2 then -h1 - h2 else f.f x)
          (insert (h0 + h1 + h2) (↑f.E1 \ insert h0 ↑f.E0)) (insert (-h1 - h2) (↑f.E2 \ insert h1 (insert (h0 + h1 + h2) ↑f.E1))) by
        convert this.insert _
        · simp
        · simp [hne1, hnotmem]
      suffices Set.BijOn (fun x ↦ if x = h1 then h2 else if x = h0 + h1 + h2 then -h1 - h2 else f.f x)
          (↑f.E1 \ insert h0 ↑f.E0) (↑f.E2 \ insert h1 (insert (h0 + h1 + h2) ↑f.E1)) by
        convert this.insert _ using 2
        · simp [sum_ne_h1]
        · simp [sum_ne_h1, hne1, hnotmem3]
      rw [Set.insert_comm]
      nth_rw 2 [Set.diff_insert_of_not_mem]
      rw [Set.insert_eq, Set.insert_eq, Set.union_comm, ← Set.diff_diff, Set.union_comm, ← Set.diff_diff]
      suffices Set.BijOn (fun x ↦ if x = h1 then h2 else if x = h0 + h1 + h2 then -h1 - h2 else f.f x)
          (↑f.E1 \ ↑f.E0) (↑f.E2 \ ↑f.E1) by
        convert this.sdiff_singleton (a := h0) _
        · simp [h0_ne_h1, h0_ne_sum]
        · simp [hE0, hE1]
      apply f.f_bijOn.congr
      intro x hx
      aesop (add forward safe PartialSolution.E1_subset_E2)
      exact hnotmem2
    · simp only [Set.mem_insert_iff, hne2.symm, Finset.mem_coe, false_or, not_or]
      exact ⟨fun nh ↦ hnotmem3 (nh ▸ h1_in_E2), fun nh ↦ hnotmem3 (f.E1_subset_E2 nh)⟩
    · simp only [Set.mem_insert_iff, self_eq_add_left, Finset.mem_coe, not_or]
      sorry
    · sorry
    · sorry
  }

def add_e1 (f : PartialSolution ℤ) (h0 h1 : ℤ) (hh0 : h0 ∉ f.E2) (hh1 : h1 ∉ f.E2)
    (hne : h0 ≠ h1) (hadd : h0 + h1 ≠ 0) : PartialSolution ℤ where
  E0 := f.E0
  E1 := f.E1 ∪ {h0}
  E2 := f.E2 ∪ {h0, h1}
  f := fun x ↦ if x = h0 then h1 else f.f x
  E0_subset_E1 := by intro; aesop (add forward safe PartialSolution.E0_subset_E1)
  E1_subset_E2 := by intro; aesop (add forward safe PartialSolution.E1_subset_E2)
  zero_mem_E0 := by simp [f.zero_mem_E0]
  f_ne_neg := by
    intro x hx
    dsimp only
    split
    · omega
    · apply f.f_ne_neg
      aesop
  maps_E0_E1 := by
    apply Set.MapsTo.mono_right _ (Finset.subset_union_left)
    apply f.maps_E0_E1.congr
    intro x hx
    aesop (add forward safe [PartialSolution.E0_subset_E2])
  maps_E1_E2 := by
    simp only [Finset.coe_union]
    apply Set.MapsTo.union_union
    · apply f.maps_E1_E2.congr
      intro x hx
      aesop (add forward safe PartialSolution.E1_subset_E2)
    · intro x hx
      aesop
  eq_f_mem_E1 := by
    intro h hh
    dsimp only
    rw [if_neg, if_neg]
    · simp [f.eq_f_mem_E1 h hh]
    · have := f.maps_E0_E1 hh
      simp_all only [ne_eq, Finset.mem_coe]
      intro a
      subst a
      exact hh0 (f.E1_subset_E2 this)
    · simp_all only [ne_eq]
      intro a
      subst a
      exact hh0 (f.E0_subset_E2 hh)
  eq_f_eq_zero := by
    intro h hh
    dsimp only
    rw [if_neg, if_neg, if_neg]
    · simp [f.eq_f_eq_zero h hh]
    · intro nh
      subst nh
      exact hh0 (f.E1_subset_E2 (f.eq_f_mem_E1 h hh))
    · simp_all only [ne_eq, Finset.mem_coe]
      intro a
      subst a
      exact hh0 (f.maps_E0_E2 hh)
    · simp_all only [ne_eq]
      intro a
      subst a
      exact hh0 (f.E0_subset_E2 hh)
  f_bijOn := by
    simp only [Finset.coe_union, Finset.coe_singleton, Set.union_singleton, Finset.union_insert,
      Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, true_or, Set.insert_diff_of_mem]
    rw [Set.insert_diff_of_not_mem, Set.insert_diff_of_not_mem, Set.diff_insert_of_not_mem]
    · suffices Set.BijOn (fun x ↦ if x = h0 then h1 else f.f x) (↑f.E1 \ ↑f.E0) (↑f.E2 \ ↑f.E1) by
        convert this.insert _
        · simp
        · simp [hh1]
      apply f.f_bijOn.congr
      intro x hx
      aesop (add forward safe PartialSolution.E1_subset_E2)
    · exact hh0
    · simp [hne.symm]
      exact hh1 ∘ (f.E1_subset_E2 ·)
    · exact hh0 ∘ (f.E0_subset_E2 ·)


-- theorem lemma721 (f : PartialSolution G) (h0 : G) (hh : h0 ∉ f.E2) :
--     ∃ g ≥ f, h0 ∈ g.E0 := by classical
--   obtain ⟨h1, hh1⟩ := Infinite.exists_not_mem_finset (f.E2 ∪ {h0, -h0})
--   obtain ⟨h2, ne1, ne2, ne3, nin1, nin2, nin3⟩ := exists_nice_triple (f.E2 ∪ {h0, -h0, h1}) h0 h1 (by
--     rw [ne_eq, add_eq_zero_iff_eq_neg]
--     rintro rfl
--     simp at hh1
--   )
--   let f' := fun x ↦
--     if x = h0 then h1 else
--     if x = h1 then h2 else
--     if x = h0 + h1 + h2 then -h1-h2 else
--     f.f x
--   use ⟨f.E0 ∪ {h0}, f.E1 ∪ {h0, h1, h0+h1+h2}, f.E2 ∪ {h0, h1, h0+h1+h2, h2, -h1-h2}, f', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
--   · simp only [ge_iff_le, le_def, Finset.le_eq_subset, Finset.subset_union_left, true_and,
--     Finset.mem_union, Finset.mem_singleton, or_true, and_true]
--     sorry
--   · simp [f.hE0]
--   · simp [f', f.f_zero]
--     sorry
--   · intro x hx
--     simp
--     sorry
--   · intro x hx
--     sorry
--   · sorry
--   · intro h hm
--     sorry
--   · simp
--     sorry

-- theorem lemma72 (f : PartialSolution G) (h0 : G) (hh : h0 ∉ f.E0) :
--     ∃ g ≥ f, h0 ∈ g.E0 := by classical
--   by_cases hE2 : h0 ∈ f.E2
--   · obtain ⟨h1, hh1⟩ := Infinite.exists_not_mem_finset (f.E2 ∪ {h0})


--     sorry
--   · sorry
