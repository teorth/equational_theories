import equational_theories.Equations
import equational_theories.Mathlib.Data.Set.Basic
import equational_theories.Mathlib.Data.Set.Function
import Mathlib.Tactic.Abel
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Logic.Equiv.Nat

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
  le a b := a.E0 ≤ b.E0 ∧ a.E1 ≤ b.E1 ∧ a.E2 ≤ b.E2 ∧ Set.EqOn a.f b.f a.E1 -- note: eqon E1
  le_refl := by simp [Set.EqOn]
  le_trans a b c hab hbc := by aesop (add forward subset_trans safe) (add simp [Set.EqOn])

lemma le_def {a b : PartialSolution G} : a ≤ b ↔
  a.E0 ≤ b.E0 ∧ a.E1 ≤ b.E1 ∧ a.E2 ≤ b.E2 ∧ Set.EqOn a.f b.f a.E1 := Iff.rfl

lemma PartialSolution.E0_subset_E2 (a : PartialSolution G) :
    a.E0 ⊆ a.E2 := a.E0_subset_E1.trans a.E1_subset_E2

lemma PartialSolution.maps_E0_E2 (a : PartialSolution G) :
    Set.MapsTo a.f a.E0 a.E2 := a.maps_E0_E1.mono_right (a.E1_subset_E2)

lemma PartialSolution.add_ne_zero (a : PartialSolution G) (x : G) (hx : x ∈ a.E1) (hx2 : x ∉ a.E0) :
    x + a.f x ≠ 0 := by
  rw [ne_eq, add_eq_zero_iff_eq_neg']
  apply a.f_ne_neg
  simp [hx, hx2]

@[simp]
lemma zero_mem_E0 (a : PartialSolution G) : 0 ∈ a.E0 := a.zero_mem_E0

@[simp]
lemma zero_mem_E2 (a : PartialSolution G) : 0 ∈ a.E2 := by
  apply a.E0_subset_E2
  exact a.zero_mem_E0

end AddCommGroup

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
      have v5 : x + f.f x + f.f (f.f x) ≠ h1 := fun nh ↦ h1_not_in_E1 (nh ▸ f.eq_f_mem_E1 x hx)
      have v6 : x + f.f x + f.f (f.f x) ≠ h0 + h1 + h2 := fun nh ↦ hnotmem2 (f.E1_subset_E2 (nh ▸ f.eq_f_mem_E1 x hx))
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
      split_ands
      · rintro rfl
        contradiction
      · exact f.add_ne_zero _ hE1 hE0
      · exact fun nh ↦ hnotmem (f.E1_subset_E2 nh)
    · simp only [Set.mem_insert_iff, h0_ne_sum.symm, Finset.mem_coe, false_or]
      exact fun nh ↦ hnotmem2 (f.E0_subset_E2 nh)
    · simp only [Set.mem_insert_iff, h0_ne_h1.symm, Finset.mem_coe, false_or]
      exact fun nh ↦ h1_not_in_E1 (f.E0_subset_E1 nh)
  }

lemma le_move_e1_e0 (f : PartialSolution ℤ) (h0 h2 : ℤ) (hE0 : h0 ∉ f.E0) (hE1 : h0 ∈ f.E1)
    (hne1 : h2 ≠ -f.f h0 - h2) (hne2 : h0 + f.f h0 + h2 ≠ -f.f h0 - h2)
    (hnotmem : h2 ∉ f.E2) (hnotmem2 : h0 + f.f h0 + h2 ∉ f.E2) (hnotmem3 : -f.f h0 - h2 ∉ f.E2) :
    f ≤ move_e1_e0 f h0 h2 hE0 hE1 hne1 hne2 hnotmem hnotmem2 hnotmem3 := by
  simp [move_e1_e0, le_def]
  simp_all only [ne_eq, Finset.subset_iff, Finset.mem_union, Finset.mem_singleton, true_or, implies_true,
    Finset.mem_insert, or_true, true_and]
  intro x hx
  dsimp only
  rw [if_neg, if_neg]
  · intro nh
    exact hnotmem2 (f.E1_subset_E2 (nh ▸ hx))
  · rintro rfl
    exact (f.f_bijOn.mapsTo ⟨hE1, hE0⟩).2 hx

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

lemma le_add_e1 (f : PartialSolution ℤ) (h0 h1 : ℤ) (hh0 : h0 ∉ f.E2) (hh1 : h1 ∉ f.E2)
    (hne : h0 ≠ h1) (hadd : h0 + h1 ≠ 0) :
    f ≤ add_e1 f h0 h1 hh0 hh1 hne hadd := by
  simp [add_e1, le_def]
  simp_all only [ne_eq, Finset.subset_iff, Finset.mem_union, Finset.mem_singleton, true_or,
    implies_true, Finset.mem_insert, or_true, true_and]
  intro x hx
  dsimp only
  rw [if_neg]
  rintro rfl
  exact hh0 (f.E1_subset_E2 hx)

open Pointwise

private theorem exists_nice_triple (S : Finset ℤ) (h0 h1 : ℤ) :
  ∃ h2, h2 ≠ -h1 -h2 ∧ h0 + h1 + h2 ≠ -h1 -h2 ∧
    h2 ∉ S ∧ h0 + h1 + h2 ∉ S ∧ -h1 -h2 ∉ S := by
  obtain ⟨h2, hh2⟩ := Infinite.exists_not_mem_finset (S ∪ {-h1/2, -h0/2-h1} ∪ (-h1 +ᵥ -S) ∪ ((-h0 + -h1) +ᵥ S))
  use h2
  simp only [Finset.union_assoc, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_vadd_finset,
    Finset.mem_neg', vadd_eq_add, not_or, not_exists, not_and] at hh2
  split_ands
  · omega
  · omega
  · exact hh2.1
  · intro nh
    replace hh2 := hh2.2.2.2 (h0 + h1 + h2) nh
    omega
  · intro nh
    replace hh2 := hh2.2.2.1 (h1 + h2) (by simpa [add_comm])
    omega

theorem lemma720 (f : PartialSolution ℤ) (h0 : ℤ) (hh : h0 ∈ f.E0) :
    ∃ g ≥ f, h0 ∈ g.E0 := by use f

theorem lemma721 (f : PartialSolution ℤ) (h0 : ℤ) (hh : h0 ∈ f.E1) (hnh : h0 ∉ f.E0) :
    ∃ g ≥ f, h0 ∈ g.E0 := by
  obtain ⟨h2, ne1, ne2, m1, m2, m3⟩ := exists_nice_triple f.E2 h0 (f.f h0)
  use move_e1_e0 f h0 h2 hnh hh ne1 ne2 m1 m2 m3, le_move_e1_e0 ..
  simp [move_e1_e0]


theorem lemma722 (f : PartialSolution ℤ) (h0 : ℤ) (hnh : h0 ∉ f.E2) :
    ∃ g ≥ f, h0 ∈ g.E0 := by
  obtain ⟨h1, hh1⟩ := Infinite.exists_not_mem_finset (f.E2 ∪ {h0, -h0})
  simp only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
    not_or] at hh1
  let f' := add_e1 f h0 h1 hnh hh1.2.1 (Ne.symm hh1.1) (by simp [add_eq_zero_iff_eq_neg', hh1])
  obtain ⟨g, hg1, hg2⟩ := lemma721 f' h0 (by simp [f', add_e1])
    (by simp only [add_e1, Finset.union_insert, f']; intro nh; exact hnh (f.E0_subset_E2 nh))
  use g, (le_add_e1 ..).trans hg1, hg2

theorem lemma723 (f : PartialSolution ℤ) (h0 : ℤ) (hh : h0 ∈ f.E2) (hnh : h0 ∉ f.E1) :
    ∃ g ≥ f, h0 ∈ g.E0 := by
  obtain ⟨x', hx'1, hx'2⟩ := f.f_bijOn.surjOn ⟨hh, hnh⟩
  obtain ⟨f', hf'1, hf'2⟩ := lemma721 f x' hx'1.1 hx'1.2
  replace hx'2 : f'.f x' = h0 := by
    subst hx'2
    apply hf'1.2.2.2.symm
    exact hx'1.1
  by_cases hh0 : h0 ∈ f'.E0
  · use f'
  obtain ⟨g, hg1, hg2⟩ := lemma721 f' h0 (hx'2 ▸ f'.maps_E0_E1 hf'2) hh0
  use g, hf'1.trans hg1, hg2

theorem lemma72 (f : PartialSolution ℤ) (h0 : ℤ) :
    ∃ g ≥ f, h0 ∈ g.E0 := by
  by_cases hE2 : h0 ∉ f.E2
  · apply lemma722 _ _ hE2
  by_cases hE1 : h0 ∉ f.E1
  · apply lemma723 <;> simp_all
  by_cases hE0 : h0 ∉ f.E0
  · apply lemma721 <;> simp_all
  · apply lemma720
    simp_all

noncomputable def closureSeq (f : PartialSolution ℤ) : ℕ → PartialSolution ℤ
| 0 => f
| n+1 => (lemma72 (closureSeq f n) (Equiv.intEquivNat.symm n)).choose

lemma closureSeq_le_closureSeq_succ (f : PartialSolution ℤ) (n : ℕ) :
    closureSeq f n ≤ closureSeq f (n + 1) :=
  (Exists.choose_spec <| lemma72 (closureSeq f n) (Equiv.intEquivNat.symm n)).1

lemma mem_closureSeq_e0 (f : PartialSolution ℤ) (n : ℤ) :
    n ∈ (closureSeq f (Equiv.intEquivNat n + 1)).E0 := by
  simp only [closureSeq, ge_iff_le, Equiv.symm_apply_apply]
  generalize_proofs pf
  exact pf.choose_spec.2

lemma closureSeq_mono (f : PartialSolution ℤ) : Monotone (closureSeq f) := by
  intro n m hnm
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction m
  case zero => simp
  case succ m hm =>
    apply hm.trans
    rw [← add_assoc]
    apply closureSeq_le_closureSeq_succ

lemma le_closureSeq (f : PartialSolution ℤ) (n : ℕ) :f ≤ closureSeq f n :=
  closureSeq_mono f (Nat.zero_le n)

noncomputable def closure (f : PartialSolution ℤ) : ℤ → ℤ :=
  fun n ↦ (closureSeq f (Equiv.intEquivNat n + 1)).f n

lemma closure_eq_of_mem_e1 (f : PartialSolution ℤ) (n : ℕ) (x : ℤ) (hn : x ∈ (closureSeq f n).E1) :
    closure f x = (closureSeq f n).f x := by
  simp [closure]
  rcases le_total n (Equiv.intEquivNat x + 1) with h | h
  · apply (closureSeq_mono f h).2.2.2.symm
    apply hn
  · apply (closureSeq_mono f h).2.2.2
    apply PartialSolution.E0_subset_E1
    exact mem_closureSeq_e0 f x

lemma lemma73 (f : PartialSolution ℤ) :
    ∃ g : ℤ → ℤ, Set.EqOn g f.f f.E1 ∧ ∀ h, g h + g (g h) + g (h + g h + g (g h)) = 0 := by
  use closure f
  constructor
  · intro x hx
    rw [closure, eq_comm]
    apply (le_closureSeq f (Equiv.intEquivNat x + 1)).2.2.2 hx
  · intro x
    rw [closure_eq_of_mem_e1 f (Equiv.intEquivNat x + 1), closure_eq_of_mem_e1 f (Equiv.intEquivNat x + 1),
      closure_eq_of_mem_e1 f (Equiv.intEquivNat x + 1)]
    · apply (closureSeq f (Equiv.intEquivNat x + 1)).eq_f_eq_zero
      apply mem_closureSeq_e0
    · apply (closureSeq f (Equiv.intEquivNat x + 1)).eq_f_mem_E1
      apply mem_closureSeq_e0
    · apply (closureSeq f (Equiv.intEquivNat x + 1)).maps_E0_E1
      apply mem_closureSeq_e0
    · apply (closureSeq f (Equiv.intEquivNat x + 1)).E0_subset_E1
      apply mem_closureSeq_e0

def initial : PartialSolution ℤ where
  E0 := {0, 1, 2}
  E1 := {0, 1, 2, 3, 4, 10, 12}
  E2 := {0, 1, 2, 3, 4, 5, 7, 10, 12, -9, -10} -- note, add h2 to blueprint
  E0_subset_E1 := by decide
  E1_subset_E2 := by decide
  f x := if x = 1 then 1 else 0
