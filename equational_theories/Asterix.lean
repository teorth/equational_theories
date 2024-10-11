import equational_theories.Equations
import equational_theories.Mathlib.Data.Set.Basic
import equational_theories.Mathlib.Data.Set.Function
import equational_theories.Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Logic.Equiv.Nat
import Mathlib.Logic.Denumerable

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
  undef_of_not_mem_E0' : ∀ x ∈ E1 \ E0, (x.2, f x.1 x.2) ∉ E1
  strange: ∀ x ∈ E1, f x.1 x.2 = x.1 → ((x.2, x.2) ∈ E1 ∧ f x.2 x.2 = x.1)

abbrev PartialSolution.g (f : PartialSolution G) : G × G → G × G :=
  fun (x, y) => (y, f.f x y)

instance : Preorder (PartialSolution G) where
  le a b := a.E0 ≤ b.E0 ∧ a.E1 ≤ b.E1 ∧ Set.EqOn a.f.uncurry b.f.uncurry a.E1
  le_refl := by simp [Set.EqOn]
  le_trans a b c hab hbc := by aesop (add forward subset_trans safe) (add simp [Set.EqOn])

lemma PartialSolution.le_def {a b : PartialSolution G} : a ≤ b ↔
  a.E0 ≤ b.E0 ∧ a.E1 ≤ b.E1 ∧ Set.EqOn a.f.uncurry b.f.uncurry a.E1 := Iff.rfl

lemma PartialSolution.t_mem_of_mem_E0 (f : PartialSolution G) {x : G × G} (hx : x ∈ f.E0) :
    f.g x ∈ f.E1 := f.t_mem_of_mem_E0' x hx

lemma PartialSolution.undef_of_not_mem_E0 (f : PartialSolution G) (x : G × G) (hx : x ∉ f.E0)
    (hx2 : x ∈ f.E1) : f.g x ∉ f.E1 := f.undef_of_not_mem_E0' x (by simp [*])

def PartialSolution.move_rev_good (f : PartialSolution G) (x y : G) (z : G) (h1 : (y, x) ∉ f.E1)
    (h2 : (x, y) ∈ f.E1 → f.f x y ≠ x) (hz1 : ∀ x ∈ f.E1, x.2 ≠ z)
    (hz2 : ∀ x ∈ f.E1, f.f x.1 x.2 ≠ z) (hz3 : ∀ x ∈ f.E1, x.1 ≠ z)
    (hzx : z ≠ x) (hzy : z ≠ y) : PartialSolution G :=
  let f' y' x' := if y' = y ∧ x' = x then z else if x' = z then y else f.f y' x'
  have f'_of_mem_E1 {a b : G} (ha : (a, b) ∈ f.E1) : f' a b = f.f a b := by
    dsimp [f']
    rw [if_neg, if_neg]
    · apply hz1 _ ha
    · rintro ⟨rfl, rfl⟩
      exact h1 ha
  have f'_of_mem_E0 {a b : G} (ha : (a, b) ∈ f.E0) : f' a b = f.f a b := f'_of_mem_E1 (f.E0_subset_E1 ha)
  have f'_y_x : f' y x = z := by simp [f']
  have f'_z {a : G} : f' a z = y := by simp [f', hzx]
  {
  E0 := f.E0 ∪ (f.E1.filter fun ⟨y', x'⟩ ↦ x' = y ∧ f.f y' x' = x)
  E1 := f.E1 ∪ {(y, x), (z, z)} ∪ (f.E1.filter fun ⟨y', x'⟩ ↦ x' = y ∧ f.f y' x' = x).image fun ⟨y', _⟩ ↦ (y', z)
  f := f'
  E0_subset_E1 := by
    rw [Finset.union_assoc]
    trans f.E1
    · apply Finset.union_subset
      exact f.E0_subset_E1
      apply Finset.filter_subset
    · exact Finset.subset_union_left
  t_mem_of_mem_E0' := by
    rintro ⟨x', y'⟩ ha
    simp only [Finset.mem_union, Finset.mem_filter] at ha
    rcases ha with ha | ⟨ha, rfl, rfl⟩
    · dsimp only
      rw [f'_of_mem_E0 ha]
      simp [f.t_mem_of_mem_E0 ha]
    · dsimp only
      rw [f'_of_mem_E1 ha]
      simp
  mem_2_of_mem_E0 := by
    rintro ⟨x', y'⟩ ha
    simp only [Finset.mem_union, Finset.mem_filter] at ha
    rcases ha with ha | ⟨ha, rfl, rfl⟩
    · dsimp only
      rw [f'_of_mem_E0 ha, f'_of_mem_E1 (f.t_mem_of_mem_E0 ha)]
      simp only [Finset.union_insert, Finset.insert_union, Finset.union_assoc, Finset.mem_insert,
        Prod.mk.injEq, Finset.mem_union, f.mem_2_of_mem_E0 _ ha, Finset.mem_singleton,
        Finset.mem_image, Finset.mem_filter, Prod.exists, exists_and_right, true_or, or_true]
    · dsimp only
      rw [f'_of_mem_E1 ha, f'_y_x]
      apply Finset.mem_union_right
      simp only [Finset.mem_image, Finset.mem_filter, Prod.mk.injEq, and_true, Prod.exists,
        exists_and_right, exists_eq_right]
      use y'
  eq_of_mem_E0 := by
    rintro ⟨x', y'⟩ ha
    simp only [Finset.mem_union, Finset.mem_filter] at ha
    rcases ha with ha | ⟨ha, rfl, rfl⟩
    · dsimp only
      rw [f'_of_mem_E0 ha, f'_of_mem_E1 (f.t_mem_of_mem_E0 ha), f'_of_mem_E1 (f.mem_2_of_mem_E0 _ ha)]
      apply f.eq_of_mem_E0 _ ha
    · dsimp only
      rw [f'_of_mem_E1 ha, f'_y_x, f'_z]
  undef_of_not_mem_E0' := by
    rintro ⟨x', y'⟩ ha
    dsimp only
    simp only [Finset.union_insert, Finset.insert_union, Finset.union_assoc, Finset.mem_sdiff,
      Finset.mem_insert, Prod.mk.injEq, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_filter, Prod.exists, exists_and_right, not_or, not_and] at ha
    obtain ⟨⟨rfl, rfl⟩ | ha | ⟨rfl, rfl⟩ | ⟨a, ⟨⟨x, ha, rfl, rfl⟩, rfl, rfl⟩⟩, ha2, ha3⟩ := ha
    · rw [f'_y_x]
      intro mem
      simp only [Finset.union_insert, Finset.insert_union, Finset.union_assoc, Finset.mem_insert,
        Prod.mk.injEq, Finset.mem_union, Finset.mem_singleton, and_true, Finset.mem_image,
        Finset.mem_filter, Prod.exists, exists_and_right, exists_eq_right] at mem
      obtain ⟨rfl, rfl⟩ | mem | rfl | ⟨x, mem, rfl, mem2⟩ := mem
      · exact hzx rfl
      · exact hz1 _ mem rfl
      · exact hzx rfl
      · exact h2 mem mem2
    · rw [f'_of_mem_E1 ha]
      intro mem
      simp only [Finset.union_insert, Finset.insert_union, Finset.union_assoc, Finset.mem_insert,
        Prod.mk.injEq, Finset.mem_union, Finset.mem_singleton, Finset.mem_image, Finset.mem_filter,
        Prod.exists, exists_and_right] at mem
      obtain ⟨rfl, rfl⟩ | mem | ⟨rfl, mem⟩ | ⟨x, -, rfl, mem2⟩ := mem
      · exact ha3 ha rfl rfl
      · exact f.undef_of_not_mem_E0 _ ha2 ha mem
      · exact hz1 _ ha rfl
      · exact hz2 _ ha mem2.symm
    · rw [f'_z]
      intro mem
      simp only [Finset.union_insert, Finset.insert_union, Finset.union_assoc, Finset.mem_insert,
        Prod.mk.injEq, Finset.mem_union, Finset.mem_singleton, true_and, Finset.mem_image,
        Finset.mem_filter, Prod.exists, exists_and_right] at mem
      obtain ⟨rfl, rfl⟩ | mem | ⟨rfl, mem⟩ | ⟨x, mem, rfl, rfl⟩ := mem
      · exact hzx rfl
      · exact hz3 _ mem rfl
      · exact hzy rfl
      · exact hzy rfl
    · rw [f'_z]
      intro mem
      simp only [Finset.union_insert, Finset.insert_union, Finset.union_assoc, Finset.mem_insert,
        Prod.mk.injEq, Finset.mem_union, Finset.mem_singleton, true_and, Finset.mem_image,
        Finset.mem_filter, Prod.exists, exists_and_right] at mem
      obtain ⟨rfl, mem⟩ | mem | ⟨rfl, mem⟩ | ⟨x, mem, rfl, rfl⟩ := mem
      · exact hzy rfl
      · exact hz3 _ mem rfl
      · exact hzy rfl
      · exact hzy rfl
  strange := by
    rintro ⟨x', y'⟩ ha heq
    simp only [Finset.union_insert, Finset.insert_union, Finset.union_assoc, Finset.mem_insert,
      Prod.mk.injEq, Finset.mem_union, Finset.mem_singleton, Finset.mem_image, Finset.mem_filter,
      Prod.exists, exists_and_right] at ha
    dsimp only at heq ⊢
    obtain ⟨rfl, rfl⟩ | ha | ⟨rfl, rfl⟩ | ⟨a, ⟨⟨x, -, rfl, rfl⟩, rfl, rfl⟩⟩ := ha
    · exact (hzy (f'_y_x ▸ heq)).elim
    · rw [f'_of_mem_E1 ha] at heq
      have v := f.strange _ ha heq
      dsimp at v
      simp only [Finset.union_insert, Finset.insert_union, Finset.union_assoc, Finset.mem_insert,
        Prod.mk.injEq, Finset.mem_union, v, Finset.mem_singleton, and_self, Finset.mem_image,
        Finset.mem_filter, Prod.exists, exists_and_right, true_or, or_true, f'_of_mem_E1]
    · simp only [Finset.union_insert, Finset.insert_union, Finset.union_assoc, Finset.mem_insert,
      Prod.mk.injEq, Finset.mem_union, Finset.mem_singleton, Finset.mem_image, Finset.mem_filter,
      and_true, Prod.exists, exists_and_right, exists_eq_right, true_or, or_true, heq, and_self]
    · simp only [Finset.union_insert, Finset.insert_union, Finset.union_assoc, Finset.mem_insert,
      Prod.mk.injEq, Finset.mem_union, Finset.mem_singleton, Finset.mem_image, Finset.mem_filter,
      and_true, Prod.exists, exists_and_right, exists_eq_right, true_or, or_true, f'_z, true_and]
      rw [← heq, f'_z]
  }

lemma PartialSolution.le_move_rev_good (f : PartialSolution G) (x y : G) (z : G) (h1 : (y, x) ∉ f.E1)
    (h2 : (x, y) ∈ f.E1 → f.f x y ≠ x) (hz1 : ∀ x ∈ f.E1, x.2 ≠ z)
    (hz2 : ∀ x ∈ f.E1, f.f x.1 x.2 ≠ z) (hz3 : ∀ x ∈ f.E1, x.1 ≠ z)
    (hzx : z ≠ x) (hzy : z ≠ y) :
    f ≤ f.move_rev_good x y z h1 h2 hz1 hz2 hz3 hzx hzy := by
  simp only [move_rev_good, Finset.union_assoc, le_def, Finset.le_eq_subset,
    Finset.subset_union_left, true_and]
  rintro ⟨x', y'⟩ mem
  simp only [Function.uncurry_apply_pair]
  rw [if_neg, if_neg]
  · exact hz1 _ mem
  · rintro ⟨rfl, rfl⟩
    exact h1 mem

lemma PartialSolution.mem_move_rev_good (f : PartialSolution G) (x y : G) (z : G) (h1 : (y, x) ∉ f.E1)
    (h2 : (x, y) ∈ f.E1 → f.f x y ≠ x) (hz1 : ∀ x ∈ f.E1, x.2 ≠ z)
    (hz2 : ∀ x ∈ f.E1, f.f x.1 x.2 ≠ z) (hz3 : ∀ x ∈ f.E1, x.1 ≠ z)
    (hzx : z ≠ x) (hzy : z ≠ y) :
    (y, x) ∈ (f.move_rev_good x y z h1 h2 hz1 hz2 hz3 hzx hzy).E1 := by
  simp [move_rev_good]

lemma PartialSolution.mem_move_rev_good_of_app_eq (f : PartialSolution G) (x y : G) (z : G) (h1 : (y, x) ∉ f.E1)
    (h2 : (x, y) ∈ f.E1 → f.f x y ≠ x) (hz1 : ∀ x ∈ f.E1, x.2 ≠ z)
    (hz2 : ∀ x ∈ f.E1, f.f x.1 x.2 ≠ z) (hz3 : ∀ x ∈ f.E1, x.1 ≠ z)
    (hzx : z ≠ x) (hzy : z ≠ y) (a : G) (hbm : (a, y) ∈ f.E1) (hp : f.f a y = x) :
    (a, y) ∈ (f.move_rev_good x y z h1 h2 hz1 hz2 hz3 hzx hzy).E0 := by
  simp [move_rev_good, hbm, hp]

def PartialSolution.move_rev_bad (f : PartialSolution G) (x y : G) (z : G) (h1 : (y, x) ∉ f.E1)
    (h2 : (x, y) ∈ f.E1) (h22 : f.f x y = x) (hz1 : ∀ x ∈ f.E1, x.2 ≠ z)
    (hz2 : ∀ x ∈ f.E1, f.f x.1 x.2 ≠ z) (hz3 : ∀ x ∈ f.E1, x.1 ≠ z)
    (hzx : z ≠ x) (hzy : z ≠ y) : PartialSolution G :=
  let f' y' x' := if y' = y ∧ x' = x then z else if x' = z then y else f.f y' x'
  have f'_of_mem_E1 {a b : G} (ha : (a, b) ∈ f.E1) : f' a b = f.f a b := by
    dsimp [f']
    rw [if_neg, if_neg]
    · apply hz1 _ ha
    · rintro ⟨rfl, rfl⟩
      exact h1 ha
  have f'_of_mem_E0 {a b : G} (ha : (a, b) ∈ f.E0) : f' a b = f.f a b := f'_of_mem_E1 (f.E0_subset_E1 ha)
  have f'_y_x : f' y x = z := by simp [f']
  have f'_z {a : G} : f' a z = y := by simp [f', hzx]
  {
  E0 := f.E0 ∪ {(y, x)} ∪ (f.E1.filter fun ⟨y', x'⟩ ↦ x' = y ∧ f.f y' x' = x)
  E1 := f.E1 ∪ {(y, x), (z, z)} ∪ (f.E1.filter fun ⟨y', x'⟩ ↦ x' = y ∧ f.f y' x' = x).image fun ⟨y', _⟩ ↦ (y', z)
  f := f'
  E0_subset_E1 := by
    nth_rw 2 [Finset.union_assoc]
    apply Finset.union_subset
    apply Finset.union_subset
    · trans f.E1
      exact f.E0_subset_E1
      exact Finset.subset_union_left
    · trans {(y, x), (z, z)}
      simp only [Finset.singleton_subset_iff, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq, true_or]
      exact fun x hx ↦ Finset.mem_union_right _ (Finset.mem_union_left _ hx)
    · trans f.E1
      apply Finset.filter_subset
      exact Finset.subset_union_left
  t_mem_of_mem_E0' := by
    rintro ⟨x', y'⟩ ha
    simp only [Finset.union_assoc, Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq,
      Finset.mem_filter] at ha
    rcases ha with ha | ⟨rfl, rfl⟩ | ⟨ha, rfl, rfl⟩
    · dsimp only
      rw [f'_of_mem_E0 ha]
      simp [f.t_mem_of_mem_E0 ha]
    · simp only [Finset.union_insert, Finset.insert_union, Finset.union_assoc, Finset.mem_insert,
      Prod.mk.injEq, Finset.mem_union, Finset.mem_singleton, Finset.mem_image, Finset.mem_filter,
      Prod.exists, exists_and_right]
      right; right; right
      use y'
      simp only [f'_y_x, and_self, and_true]
      use x'
    · dsimp only
      rw [f'_of_mem_E1 ha]
      simp
  mem_2_of_mem_E0 := by
    rintro ⟨x', y'⟩ ha
    simp only [Finset.union_assoc, Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq,
      Finset.mem_filter] at ha
    rcases ha with ha | ⟨rfl, rfl⟩ | ⟨ha, rfl, rfl⟩
    · dsimp only
      rw [f'_of_mem_E0 ha, f'_of_mem_E1 (f.t_mem_of_mem_E0 ha)]
      simp only [Finset.union_insert, Finset.insert_union, Finset.union_assoc, Finset.mem_insert,
        Prod.mk.injEq, Finset.mem_union, f.mem_2_of_mem_E0 _ ha, Finset.mem_singleton,
        Finset.mem_image, Finset.mem_filter, Prod.exists, exists_and_right, true_or, or_true]
    · simp only [Finset.union_insert, Finset.insert_union, Finset.union_assoc, f'_y_x, f'_z,
      Finset.mem_insert, Prod.mk.injEq, true_and, Finset.mem_union, f.strange _ h2 h22,
      Finset.mem_singleton, and_self, Finset.mem_image, Finset.mem_filter, Prod.exists,
      exists_and_right, true_or, or_true]
    · dsimp only
      rw [f'_of_mem_E1 ha, f'_y_x]
      apply Finset.mem_union_right
      simp only [Finset.mem_image, Finset.mem_filter, Prod.mk.injEq, and_true, Prod.exists,
        exists_and_right, exists_eq_right]
      use y'
  eq_of_mem_E0 := by
    rintro ⟨x', y'⟩ ha
    simp only [Finset.union_assoc, Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq,
      Finset.mem_filter] at ha
    rcases ha with ha | ⟨rfl, rfl⟩ | ⟨ha, rfl, rfl⟩
    · dsimp only
      rw [f'_of_mem_E0 ha, f'_of_mem_E1 (f.t_mem_of_mem_E0 ha), f'_of_mem_E1 (f.mem_2_of_mem_E0 _ ha)]
      apply f.eq_of_mem_E0 _ ha
    · simp only [f'_y_x, f'_z, f.strange _ h2 h22, f'_of_mem_E1]
    · dsimp only
      rw [f'_of_mem_E1 ha, f'_y_x, f'_z]
  undef_of_not_mem_E0' := by
    rintro ⟨x', y'⟩ ha
    dsimp only
    simp only [Finset.union_insert, Finset.insert_union, Finset.union_assoc, Finset.mem_sdiff,
      Finset.mem_insert, Prod.mk.injEq, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_filter, Prod.exists, exists_and_right, not_or, not_and] at ha
    obtain ⟨⟨rfl, rfl⟩ | ha | ⟨rfl, rfl⟩ | ⟨a, ⟨⟨x, ha, rfl, rfl⟩, rfl, rfl⟩⟩, ha2, ha3, ha4⟩ := ha
    · simp at ha3
    · rw [f'_of_mem_E1 ha]
      intro mem
      simp only [Finset.union_insert, Finset.insert_union, Finset.union_assoc, Finset.mem_insert,
        Prod.mk.injEq, Finset.mem_union, Finset.mem_singleton, Finset.mem_image, Finset.mem_filter,
        Prod.exists, exists_and_right] at mem
      obtain ⟨rfl, rfl⟩ | mem | ⟨rfl, mem⟩ | ⟨x, -, rfl, mem2⟩ := mem
      · exact ha4 ha rfl rfl
      · exact f.undef_of_not_mem_E0 _ ha2 ha mem
      · exact hz1 _ ha rfl
      · exact hz2 _ ha mem2.symm
    · rw [f'_z]
      intro mem
      simp only [Finset.union_insert, Finset.insert_union, Finset.union_assoc, Finset.mem_insert,
        Prod.mk.injEq, Finset.mem_union, Finset.mem_singleton, true_and, Finset.mem_image,
        Finset.mem_filter, Prod.exists, exists_and_right] at mem
      obtain ⟨rfl, rfl⟩ | mem | ⟨rfl, mem⟩ | ⟨x, mem, rfl, rfl⟩ := mem
      · exact hzx rfl
      · exact hz3 _ mem rfl
      · exact hzy rfl
      · exact hzy rfl
    · rw [f'_z]
      intro mem
      simp only [Finset.union_insert, Finset.insert_union, Finset.union_assoc, Finset.mem_insert,
        Prod.mk.injEq, Finset.mem_union, Finset.mem_singleton, true_and, Finset.mem_image,
        Finset.mem_filter, Prod.exists, exists_and_right] at mem
      obtain ⟨rfl, mem⟩ | mem | ⟨rfl, mem⟩ | ⟨x, mem, rfl, rfl⟩ := mem
      · exact hzy rfl
      · exact hz3 _ mem rfl
      · exact hzy rfl
      · exact hzy rfl
  strange := by
    rintro ⟨x', y'⟩ ha heq
    simp only [Finset.union_insert, Finset.insert_union, Finset.union_assoc, Finset.mem_insert,
      Prod.mk.injEq, Finset.mem_union, Finset.mem_singleton, Finset.mem_image, Finset.mem_filter,
      Prod.exists, exists_and_right] at ha
    dsimp only at heq ⊢
    obtain ⟨rfl, rfl⟩ | ha | ⟨rfl, rfl⟩ | ⟨a, ⟨⟨x, -, rfl, rfl⟩, rfl, rfl⟩⟩ := ha
    · exact (hzy (f'_y_x ▸ heq)).elim
    · rw [f'_of_mem_E1 ha] at heq
      have v := f.strange _ ha heq
      dsimp at v
      simp only [Finset.union_insert, Finset.insert_union, Finset.union_assoc, Finset.mem_insert,
        Prod.mk.injEq, Finset.mem_union, v, Finset.mem_singleton, and_self, Finset.mem_image,
        Finset.mem_filter, Prod.exists, exists_and_right, true_or, or_true, f'_of_mem_E1]
    · simp only [Finset.union_insert, Finset.insert_union, Finset.union_assoc, Finset.mem_insert,
      Prod.mk.injEq, Finset.mem_union, Finset.mem_singleton, Finset.mem_image, Finset.mem_filter,
      and_true, Prod.exists, exists_and_right, exists_eq_right, true_or, or_true, heq, and_self]
    · simp only [Finset.union_insert, Finset.insert_union, Finset.union_assoc, Finset.mem_insert,
      Prod.mk.injEq, Finset.mem_union, Finset.mem_singleton, Finset.mem_image, Finset.mem_filter,
      and_true, Prod.exists, exists_and_right, exists_eq_right, true_or, or_true, f'_z, true_and]
      rw [← heq, f'_z]
  }

lemma PartialSolution.le_move_rev_bad (f : PartialSolution G) (x y : G) (z : G) (h1 : (y, x) ∉ f.E1)
    (h2 : (x, y) ∈ f.E1) (h22 : f.f x y = x) (hz1 : ∀ x ∈ f.E1, x.2 ≠ z)
    (hz2 : ∀ x ∈ f.E1, f.f x.1 x.2 ≠ z) (hz3 : ∀ x ∈ f.E1, x.1 ≠ z)
    (hzx : z ≠ x) (hzy : z ≠ y) :
    f ≤ f.move_rev_bad x y z h1 h2 h22 hz1 hz2 hz3 hzx hzy := by
  simp only [move_rev_bad, Finset.union_assoc, le_def, Finset.le_eq_subset,
    Finset.subset_union_left, true_and]
  rintro ⟨x', y'⟩ mem
  simp only [Function.uncurry_apply_pair]
  rw [if_neg, if_neg]
  · exact hz1 _ mem
  · rintro ⟨rfl, rfl⟩
    exact h1 mem

lemma PartialSolution.mem_move_rev_bad (f : PartialSolution G) (x y : G) (z : G) (h1 : (y, x) ∉ f.E1)
    (h2 : (x, y) ∈ f.E1) (h22 : f.f x y = x) (hz1 : ∀ x ∈ f.E1, x.2 ≠ z)
    (hz2 : ∀ x ∈ f.E1, f.f x.1 x.2 ≠ z) (hz3 : ∀ x ∈ f.E1, x.1 ≠ z)
    (hzx : z ≠ x) (hzy : z ≠ y) :
    (y, x) ∈ (f.move_rev_bad x y z h1 h2 h22 hz1 hz2 hz3 hzx hzy).E1 := by
  simp [move_rev_bad]

lemma PartialSolution.mem_move_rev_bad_of_app_eq (f : PartialSolution G) (x y : G) (z : G) (h1 : (y, x) ∉ f.E1)
    (h2 : (x, y) ∈ f.E1) (h22 : f.f x y = x) (hz1 : ∀ x ∈ f.E1, x.2 ≠ z)
    (hz2 : ∀ x ∈ f.E1, f.f x.1 x.2 ≠ z) (hz3 : ∀ x ∈ f.E1, x.1 ≠ z)
    (hzx : z ≠ x) (hzy : z ≠ y) (a : G) (hbm : (a, y) ∈ f.E1) (hp : f.f a y = x) :
    (a, y) ∈ (f.move_rev_bad x y z h1 h2 h22 hz1 hz2 hz3 hzx hzy).E0 := by
  simp [move_rev_bad, hbm, hp]


variable [Denumerable G]

def Denumerable.notMemFinset (s : Finset G) : G :=
  Denumerable.ofNat G (Nat.find (Infinite.exists_not_mem_finset (s.image Encodable.encode)))

omit [DecidableEq G] in
theorem Denumerable.notMemFinset_prop (s : Finset G) : Denumerable.notMemFinset s ∉ s := by
  simp [notMemFinset]
  intro mem
  have : Nat.find (Infinite.exists_not_mem_finset (s.image Encodable.encode)) ∈ s.image Encodable.encode := by
    simp only [Finset.mem_image, not_exists, not_and]
    refine ⟨_, mem, ?_⟩
    simp only [Denumerable.decode_eq_ofNat, Option.some.injEq, Denumerable.encode_ofNat]
  have : Nat.find (Infinite.exists_not_mem_finset (s.image Encodable.encode)) ∉ s.image Encodable.encode :=
    Nat.find_spec (Infinite.exists_not_mem_finset (s.image Encodable.encode))
  contradiction

def PartialSolution.move_rev_good' (f : PartialSolution G) (x y : G) (h1 : (y, x) ∉ f.E1)
    (h2 : (x, y) ∈ f.E1 → f.f x y ≠ x) : PartialSolution G := by -- This intentionally used `by` for data.
  let z : G := Denumerable.notMemFinset (f.E1.image (·.1) ∪ f.E1.image (·.2) ∪ f.E1.image (fun ⟨a, b⟩ ↦ f.f a b) ∪ {x, y})
  have zp := Denumerable.notMemFinset_prop (f.E1.image (·.1) ∪ f.E1.image (·.2) ∪ f.E1.image (fun ⟨a, b⟩ ↦ f.f a b) ∪ {x, y})
  change z ∉ _ at zp
  simp only [Finset.union_assoc, Finset.union_insert, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right, Finset.mem_singleton, not_or,
    not_exists, not_and] at zp
  exact f.move_rev_good x y z h1 h2 (fun x hx nh ↦ zp.2.2.1 x.1 (by convert hx; simp [nh]))
    (fun x hx ↦ zp.2.2.2.1 x.1 x.2 hx) (fun x hx nh ↦ zp.2.1 x.2 (by convert hx; simp [nh])) zp.1 zp.2.2.2.2

lemma PartialSolution.le_move_rev_good' (f : PartialSolution G) (x y : G) (h1 : (y, x) ∉ f.E1)
    (h2 : (x, y) ∈ f.E1 → f.f x y ≠ x) : f ≤ f.move_rev_good' x y h1 h2 := by
  simp [move_rev_good', le_move_rev_good]

lemma PartialSolution.mem_move_rev_good' (f : PartialSolution G) (x y : G) (h1 : (y, x) ∉ f.E1)
    (h2 : (x, y) ∈ f.E1 → f.f x y ≠ x) : (y, x) ∈ (f.move_rev_good' x y h1 h2).E1 := by
  simp [move_rev_good', mem_move_rev_good]

lemma PartialSolution.mem_move_rev_good'_of_app_eq (f : PartialSolution G) (x y : G) (h1 : (y, x) ∉ f.E1)
    (h2 : (x, y) ∈ f.E1 → f.f x y ≠ x) (a : G) (hbm : (a, y) ∈ f.E1) (hp : f.f a y = x) :
    (a, y) ∈ (f.move_rev_good' x y h1 h2).E0 := by
  simp [move_rev_good', mem_move_rev_good_of_app_eq, hbm, hp]

def PartialSolution.move_rev_bad' (f : PartialSolution G) (x y : G) (h1 : (y, x) ∉ f.E1)
    (h2 : (x, y) ∈ f.E1) (h22 : f.f x y = x) : PartialSolution G := by
  let z : G := Denumerable.notMemFinset (f.E1.image (·.1) ∪ f.E1.image (·.2) ∪ f.E1.image (fun ⟨a, b⟩ ↦ f.f a b) ∪ {x, y})
  have zp := Denumerable.notMemFinset_prop (f.E1.image (·.1) ∪ f.E1.image (·.2) ∪ f.E1.image (fun ⟨a, b⟩ ↦ f.f a b) ∪ {x, y})
  change z ∉ _ at zp
  simp only [Finset.union_assoc, Finset.union_insert, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right, Finset.mem_singleton, not_or,
    not_exists, not_and] at zp
  exact f.move_rev_bad x y z h1 h2 h22 (fun x hx nh ↦ zp.2.2.1 x.1 (by convert hx; simp [nh]))
    (fun x hx ↦ zp.2.2.2.1 x.1 x.2 hx) (fun x hx nh ↦ zp.2.1 x.2 (by convert hx; simp [nh])) zp.1 zp.2.2.2.2

lemma PartialSolution.le_move_rev_bad' (f : PartialSolution G) (x y : G) (h1 : (y, x) ∉ f.E1)
    (h2 : (x, y) ∈ f.E1) (h22 : f.f x y = x) : f ≤ f.move_rev_bad' x y h1 h2 h22 := by
  simp [move_rev_bad', le_move_rev_bad]

lemma PartialSolution.mem_move_rev_bad' (f : PartialSolution G) (x y : G) (h1 : (y, x) ∉ f.E1)
    (h2 : (x, y) ∈ f.E1) (h22 : f.f x y = x) : (y, x) ∈ (f.move_rev_bad' x y h1 h2 h22).E1 := by
  simp [move_rev_bad', mem_move_rev_bad]

lemma PartialSolution.mem_move_rev_bad'_of_app_eq (f : PartialSolution G) (x y : G) (h1 : (y, x) ∉ f.E1)
    (h2 : (x, y) ∈ f.E1) (h22 : f.f x y = x) (a : G) (hbm : (a, y) ∈ f.E1) (hp : f.f a y = x) :
    (a, y) ∈ (f.move_rev_bad' x y h1 h2 h22).E0 := by
  simp [move_rev_bad', mem_move_rev_bad_of_app_eq, hbm, hp]

def PartialSolution.act (f : PartialSolution G) (x y : G) (h1 : (y, x) ∉ f.E1) : PartialSolution G :=
    if h2 : (x, y) ∈ f.E1 → f.f x y ≠ x then f.move_rev_good' x y h1 h2 else f.move_rev_bad' x y h1 (by simp_all) (by simp_all)

lemma PartialSolution.le_act (f : PartialSolution G) (x y : G) (h1 : (y, x) ∉ f.E1) :
    f ≤ f.act x y h1 := by
  unfold act
  split
  · apply le_move_rev_good'
  · apply le_move_rev_bad'

lemma PartialSolution.mem_act (f : PartialSolution G) (x y : G) (h1 : (y, x) ∉ f.E1) :
    (y, x) ∈ (f.act x y h1).E1 := by
  unfold act
  split
  · apply mem_move_rev_good'
  · apply mem_move_rev_bad'

lemma PartialSolution.mem_act_of_app_eq (f : PartialSolution G) (x y : G) (h1 : (y, x) ∉ f.E1)
    (a : G) (hbm : (a, y) ∈ f.E1) (hp : f.f a y = x) :
    (a, y) ∈ (f.act x y h1).E0 := by
  unfold act
  split
  · apply mem_move_rev_good'_of_app_eq <;> assumption
  · apply mem_move_rev_bad'_of_app_eq <;> assumption

-- add (y, x)
def PartialSolution.add_e1 (f : PartialSolution G) (x y : G) : PartialSolution G :=
    if h1 : (y, x) ∈ f.E1 then f else f.act x y h1

lemma PartialSolution.le_add_e1 (f : PartialSolution G) (x y : G) :
    f ≤ f.add_e1 x y := by
  unfold add_e1
  split
  · rfl
  · apply le_act

lemma PartialSolution.mem_add_e1 (f : PartialSolution G) (x y : G) :
    (y, x) ∈ (f.add_e1 x y).E1 := by
  unfold add_e1
  split
  · assumption
  · apply mem_act

lemma PartialSolution.mem_add_e1_of_app_eq (f : PartialSolution G) (x y : G)
    (a : G) (hbm : (a, y) ∈ f.E1) (hp : f.f a y = x) :
    (a, y) ∈ (f.add_e1 x y).E0 := by
  unfold add_e1
  split
  · by_contra! nh
    have := f.undef_of_not_mem_E0 _ nh hbm
    apply this
    simpa [g, hp]
  · apply mem_act_of_app_eq <;> assumption

def PartialSolution.add_e0 (f : PartialSolution G) (x y : G) : PartialSolution G :=
  let f' := f.add_e1 x y
  f'.add_e1 (f'.f y x) x

lemma PartialSolution.le_add_e0 (f : PartialSolution G) (x y : G) :
    f ≤ f.add_e0 x y := by
  unfold add_e0
  dsimp only
  trans f.add_e1 x y <;>
    apply le_add_e1

lemma PartialSolution.mem_add_e0 (f : PartialSolution G) (x y : G) :
    (y, x) ∈ (f.add_e0 x y).E0 := by
  unfold add_e0
  simp only
  apply mem_add_e1_of_app_eq
  · apply mem_add_e1
  · rfl

def closureSeq (f : PartialSolution G) : ℕ → PartialSolution G
| 0 => f
| n+1 => (closureSeq f n).add_e0 (Denumerable.ofNat (G × G) n).2 (Denumerable.ofNat (G × G) n).1

lemma closureSeq_le_closureSeq_succ (f : PartialSolution G) (n : ℕ) :
    closureSeq f n ≤ closureSeq f (n + 1) :=
  PartialSolution.le_add_e0 ..

lemma mem_closureSeq_e0 (f : PartialSolution G) (a b : G) :
    (a, b) ∈ (closureSeq f (Encodable.encode (a, b) + 1)).E0 := by
  simp only [closureSeq, ge_iff_le, Equiv.symm_apply_apply, Denumerable.ofNat_encode]
  apply PartialSolution.mem_add_e0

lemma closureSeq_mono (f : PartialSolution G) : Monotone (closureSeq f) := by
  intro n m hnm
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction m
  case zero => simp
  case succ m hm =>
    apply hm.trans
    rw [← add_assoc]
    apply closureSeq_le_closureSeq_succ

lemma le_closureSeq (f : PartialSolution G) (n : ℕ) : f ≤ closureSeq f n :=
  closureSeq_mono f (Nat.zero_le n)

def closure (f : PartialSolution G) : G → G → G :=
  fun a b ↦ (closureSeq f (Encodable.encode (a, b) + 1)).f a b

lemma closure_eq_of_mem_e1 (f : PartialSolution G) (n : ℕ) (a b : G) (hn : (a, b) ∈ (closureSeq f n).E1) :
    closure f a b = (closureSeq f n).f a b := by
  simp only [closure, Prod.mk.eta]
  rcases le_total n (Encodable.encode (a, b) + 1) with h | h
  · apply (closureSeq_mono f h).2.2.symm hn
  · apply (closureSeq_mono f h).2.2 (PartialSolution.E0_subset_E1 _ (mem_closureSeq_e0 f a b))

theorem closure_prop (f : PartialSolution G) : ∀ x y, closure f x (closure f y (closure f x y)) = y := by
  intro x y
  rw [closure_eq_of_mem_e1 f (Encodable.encode (x, y) + 1) x y,
    closure_eq_of_mem_e1 f (Encodable.encode (x, y) + 1) y,
    closure_eq_of_mem_e1 f (Encodable.encode (x, y) + 1)]
  · apply PartialSolution.eq_of_mem_E0 _ (x, y)
    apply mem_closureSeq_e0
  · apply PartialSolution.mem_2_of_mem_E0 _ (x, y)
    apply mem_closureSeq_e0
  · apply PartialSolution.t_mem_of_mem_E0' _ (x, y)
    apply mem_closureSeq_e0
  · apply PartialSolution.E0_subset_E1
    apply mem_closureSeq_e0

def initial : PartialSolution ℕ where
  E0 := {(1, 0)}
  E1 := {(0, 0), (1, 0), (0, 2), (1, 3)}
  f a b := if a = 0 then (if b = 0 then 1 else 3) else if a = 1 then (if b = 0 then 2 else 0) else 0
  E0_subset_E1 := by decide
  t_mem_of_mem_E0' := by decide
  mem_2_of_mem_E0 := by decide
  eq_of_mem_E0 := by decide
  undef_of_not_mem_E0' := by decide
  strange := by decide


theorem Equation65_not_imlies_Equation359 : ∃ (G : Type) (_ : Magma G), Equation65 G ∧ ¬ Equation359 G := by
  use ℕ, ⟨closure initial⟩
  simp only [Equation65, closure_prop, implies_true, not_forall, true_and]
  use 0
  rw [closure_eq_of_mem_e1 _ 0, closure_eq_of_mem_e1 _ 0]
  · decide
  · decide
  · decide

theorem Equation65_not_imlies_Equation614 : ∃ (G : Type) (_ : Magma G), Equation65 G ∧ ¬ Equation614 G := by
  use ℕ, ⟨closure initial⟩
  simp only [Equation65, closure_prop, implies_true, not_forall, true_and]
  use 0
  rw [closure_eq_of_mem_e1 _ 0, closure_eq_of_mem_e1 _ 0]
  · decide
  · decide
  · decide
