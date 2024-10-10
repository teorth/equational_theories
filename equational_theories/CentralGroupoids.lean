/-
  Give a streamlined construction of Knuth's nonnatural central groupoid
  A2 and prove it isomorphic to a FinOp table.

  Settle a bunch of anti-implications of the form 168=>X using the latter.

  Construction based on Section 5 of
    Donald E. Knuth, Notes on central groupoids,
    Journal of Combinatorial Theory, Volume 8, Issue 4, 1970,
    https://doi.org/10.1016/S0021-9800(70)80032-1

  There is a construction of other central groupoids in progress, which
  will eventually resolve all remaining implications from 168.
-/

import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MagmaOp
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import equational_theories.Homomorphisms
import equational_theories.SmallMagmas

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Ring.Idempotents
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Data.List.TFAE
import Mathlib.Data.Set.Card
import Mathlib.Tactic.TFAE
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.Ordinal

/-- The class of magmas whose operation satisfies equation 168. -/
class CentralMagma (α : Type*) extends Magma α where
  central (x y z : α) : (x ◇ y) ◇ (y ◇ z) = y

attribute [simp] CentralMagma.central

/-- The class of directed graphs which have Property C: that for any `x, y`, there exists a unique
`z` such that `x ⟶ z ⟶ y`. We write this as a function rather than a unique existence statement
for convenience. -/
class CentralDGraph (α : Type*) extends Quiver.{0} α where
  middle : α → α → α
  to_middle (x y : α) : x ⟶ middle x y
  from_middle (x y : α) : middle x y ⟶ y
  eq_middle {x y z : α} : (x ⟶ z) → (z ⟶ y) → middle x y = z

/-- A lemma to help prove equality of two central directed graphs. -/
lemma CentralDGraph.eq {α : Type*} {h₁ : CentralDGraph α} {h₂ : CentralDGraph α}
    (hom_eq : ∀ x y, h₁.Hom x y ↔ h₂.Hom x y)
    (middle_eq : ∀ x y, h₁.middle x y = h₂.middle x y) :
    h₁ = h₂ := by
  cases' h₁ with h₁
  cases' h₁
  cases' h₂ with h₂
  cases' h₂
  congr
  · ext x y
    exact hom_eq _ _
  · ext x y
    exact middle_eq _ _

variable {α : Type*}

/-- Any central directed graph can be turned into a central multiplication. -/
def CentralDGraph.to_CentralMagma [CentralDGraph α] : CentralMagma α where
  op := middle
  central x y z := eq_middle (from_middle x y) (to_middle y z)

/-- Any type with a central multiplication can given a quiver structure.  -/
instance CentralMagma.to_quiver [CentralMagma α] : Quiver.{0} α where
  Hom x y := ∃ z, x ◇ z = y

open MulOpposite

instance MulOpposite.CentralMagma {α : Type*} [CentralMagma α] : CentralMagma αᵐᵒᵖ where
  central := fun x y z => by
    refine unop_injective ?_
    rw [unop_diw, unop_diw, unop_diw, CentralMagma.central]

namespace CentralMagma

variable [CentralMagma α] {x y z : α}

@[simp] lemma mul_mul_mul_cancel : x ◇ ((x ◇ y) ◇ z) = x ◇ y :=
  (congrArg (· ◇ ((x ◇ y) ◇ z)) (central _ _ _).symm).trans (central (x ◇ x) _ _)

@[simp] lemma mul_mul_mul_cancel' : (x ◇ (y ◇ z)) ◇ z = y ◇ z :=
  op_injective mul_mul_mul_cancel

lemma subsingleton_of_associative (h : ∀ a b c : α, (a ◇ b) ◇ c = a ◇ (b ◇ c)) : Subsingleton α :=
  Subsingleton.intro <| fun x y =>
  calc
    x = (x ◇ x) ◇ (x ◇ _) := (central _ _ _).symm
    (x ◇ x) ◇ (x ◇ _) = (_ ◇ y) ◇ (y ◇ y) := by rw [←h, ←h, ←h]
    _ = y := central _ _ _

lemma subsingleton_of_commutative (h : ∀ a b : α, a ◇ b = b ◇ a) : Subsingleton α :=
  Subsingleton.intro <| fun x y => calc
    x = (y ◇ x) ◇ (x ◇ y) := (central _ _ _).symm
    _ = (x ◇ y) ◇ (y ◇ x) := h _ _
    _ = y := central _ _ _

lemma mul_self_involution : Function.Involutive fun x : α => x ◇ x := fun x => by simp

lemma hom_iff_exists_right : (x ⟶ y) ↔ ∃ z, x ◇ z = y := Iff.rfl

lemma hom_iff_exists_left : (x ⟶ y) ↔ ∃ z, z ◇ y = x := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, central x _ _⟩
  · rintro ⟨x, rfl⟩
    refine ⟨_, central _ _ y⟩

alias ⟨_root_.Quiver.Hom.exists_left, _⟩ := hom_iff_exists_left
alias ⟨_root_.Quiver.Hom.exists_right, _⟩ := hom_iff_exists_right

/-- Any type with a central multiplication can be given a central directed graph structure. -/
instance to_centralDGraph [CentralMagma α] : CentralDGraph α where
  middle := (· ◇ ·)
  to_middle x y := ⟨y, rfl⟩
  from_middle x y := hom_iff_exists_left.2 ⟨x, rfl⟩
  eq_middle := by
    rintro x y z h ⟨_, rfl⟩
    obtain ⟨_, rfl⟩ := h.exists_left
    dsimp
    rw [central]

@[simp] lemma middle_eq_mul {x y : α} : CentralDGraph.middle x y = x ◇ y := rfl
@[simp] lemma to_mul {x y : α} : x ⟶ x ◇ y := CentralDGraph.to_middle _ _
@[simp] lemma from_mul {x y : α} : x ◇ y ⟶ y := CentralDGraph.from_middle _ _
lemma mul_eq_of_hom {x y z : α} (h₁ : x ⟶ z) (h₂ : z ⟶ y) : x ◇ y = z :=
  CentralDGraph.eq_middle h₁ h₂
lemma eq_of_homs {x y z w : α} (h₁ : x ⟶ z) (h₂ : z ⟶ y) (h₃ : x ⟶ w) (h₄ : w ⟶ y) : z = w := by
  rw [←mul_eq_of_hom h₁ h₂, mul_eq_of_hom h₃ h₄]

lemma hom_iff_eq : (x ⟶ y) ↔ x ◇ (y ◇ x) = y :=
  ⟨fun h => mul_eq_of_hom h to_mul, fun h => hom_iff_exists_right.2 ⟨_, h⟩⟩

lemma hom_iff_eq' : (x ⟶ y) ↔ (y ◇ x) ◇ y = x :=
  ⟨fun h => mul_eq_of_hom from_mul h, fun h => hom_iff_exists_left.2 ⟨_, h⟩⟩

instance [DecidableEq α] : DecidablePred (x ⟶ ·) :=
  fun _ => decidable_of_iff' _ hom_iff_eq

instance [DecidableEq α] : DecidablePred (· ⟶ x) :=
  fun _ => decidable_of_iff' _ hom_iff_eq

def CentralMagma_equiv_centralDGraph (α : Type*) : CentralMagma α ≃ CentralDGraph α where
  toFun h := to_centralDGraph
  invFun h := CentralDGraph.to_CentralMagma
  left_inv := fun h => rfl
  right_inv := fun h => by
    dsimp
    refine CentralDGraph.eq ?_ fun x y => rfl
    intro x y
    change (∃ z, CentralDGraph.middle x z = _) ↔ _
    constructor
    · rintro ⟨z, rfl⟩
      exact CentralDGraph.to_middle x z
    · intro h
      exact ⟨_, CentralDGraph.eq_middle h (CentralDGraph.to_middle y x)⟩

def Natural (α : Type*) := α × α

/-- For any type `α`, the product of `α` with itself has a central multiplication. -/
instance Product (α : Type*) : CentralMagma (Natural α) where
  op (x y : α × α) := (x.2, y.1)
  central _ _ _ := rfl

lemma product_mul {α : Type*} {x y : Natural α} : x ◇ y = (x.2, y.1) := rfl

lemma Natural.hom_iff {S : Type*} {x y : Natural S} :
    (x ⟶ y) ↔ x.2 = y.1 := by
  rw [hom_iff_eq, product_mul, product_mul, ← Prod.eta y, Prod.ext_iff]
  simp

/--
There is a set of every square finite size with a central multiplication.
-/
lemma exists_central_mul_card (n : ℕ) :
    ∃ α : Type*, Nonempty (CentralMagma α) ∧ Nat.card α = n * n :=
  ⟨Natural (ULift (Fin n)), ⟨Product _⟩, by simp [Natural]⟩

section cardinal
open scoped Cardinal

/--
There is a set of every infinite cardinality with a central multiplication.
As we later show, this does not hold for all finite cardinals.
-/
lemma exists_central_mul_cardinal (c : Cardinal) (hc : ℵ₀ ≤ c) :
    ∃ α : Type*, Nonempty (CentralMagma α) ∧ #α = c := by
  induction c using Cardinal.inductionOn
  case h α =>
    refine ⟨α × α, ⟨Product α⟩, ?_⟩
    rw [←Cardinal.mul_def, Cardinal.mul_eq_self hc]

end cardinal

def ZeroProduct.{u} (α : Type u) [DecidableEq α] [Zero α] [Mul α] [Div α] [IsLeftCancelMul α] :
  Type u := α × α

instance ZeroProduct.CentralDGraph (α : Type*) [DecidableEq α] [Zero α] [Mul α] [Div α]
    [IsLeftCancelMul α]
    (right_zero : ∀ x : α, x * 0 = 0)
    (mul_div_cancel' : ∀ x y : α, x * (y / x) = y) :
    CentralDGraph (ZeroProduct α) where
  Hom x y := (x.2 = y.1 ∧ y.2 ≠ 0) ∨ (x.1 * x.2 = y.1 ∧ y.2 = 0)
  middle x y := if y.1 = 0 then (x.1 * x.2, 0) else if y.2 = 0 then (x.2, y.1 / x.2) else (x.2, y.1)
  to_middle := by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    rcases eq_or_ne y₁ 0 with hy₁ | hy₁
    case inl => simp [hy₁]
    rcases eq_or_ne y₂ 0 with hy₂ | hy₂
    case inl =>
      simp only [hy₁, ↓reduceIte, hy₂, ne_eq, true_and]
      left
      contrapose! hy₁
      rw [← mul_div_cancel' x₂ y₁, hy₁, right_zero]
    case inr => simp [hy₁, hy₂]
  from_middle := by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    rcases eq_or_ne y₁ 0 with hy₁ | hy₁
    case inl => simp [hy₁, right_zero, em']
    rcases eq_or_ne y₂ 0 with hy₂ | hy₂
    case inl => simp [hy₁, hy₂, mul_div_cancel']
    case inr => simp [hy₁, hy₂]
  eq_middle := by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ z
    rcases eq_or_ne y₁ 0 with hy₁ | hy₁
    case inl =>
      simp (config := { contextual := true }) only [ne_eq, hy₁, ↓reduceIte, Prod.ext_iff (y := z),
        or_imp, and_true, and_imp, false_implies, true_and, implies_true, imp_self, right_zero,
        and_self]
      rintro rfl hz2 hz rfl
      exfalso
      exact hz2 (mul_left_cancel (hz.trans (right_zero _).symm))
    rcases eq_or_ne y₂ 0 with hy₂ | hy₂
    case inl =>
      simp (config := { contextual := true }) only [ne_eq, hy₂, not_true_eq_false, and_false,
        and_true, false_or, hy₁, ↓reduceIte, Prod.ext_iff (y := z), or_imp, true_and, and_imp,
        right_zero, hy₁.symm, false_implies, implies_true]
      rintro rfl _ rfl
      apply mul_left_cancel
      rw [mul_div_cancel']
    case inr =>
      simp (config := {contextual := true}) [hy₂, Prod.ext_iff (y := z), or_imp, hy₁.symm, hy₁]

lemma idempotent_iff_hom_self : x ◇ x = x ↔ (x ⟶ x) := by
  constructor
  · intro h
    rw [hom_iff_eq, h, h]
  · intro h
    exact mul_eq_of_hom h h

/--
The set of all elements which are on the right of `x`. Alternatively, the set of elements which
can be written as `x ◇ y` for some `y`.
-/
def rightElements (x : α) : Set α := {z | x ⟶ z}
/--
The set of all elements which are on the left of `x`. Alternatively, the set of elements which
can be written as `y ◇ x` for some `y`.
-/
def leftElements (x : α) : Set α := {z | z ⟶ x}

lemma mem_rightElements_iff_hom : z ∈ rightElements x ↔ (x ⟶ z) := Iff.rfl
lemma mem_leftElements_iff_hom : z ∈ leftElements x ↔ (z ⟶ x) := Iff.rfl

lemma mem_rightElements_iff_exists : z ∈ rightElements x ↔ ∃ y, x ◇ y = z :=
  hom_iff_exists_right
lemma mem_leftElements_iff_exists : z ∈ leftElements x ↔ ∃ y, y ◇ x = z :=
  hom_iff_exists_left

instance [DecidableEq α] : DecidablePred (· ∈ rightElements x) :=
  fun _ => decidable_of_iff' _ hom_iff_eq

@[simp] lemma mul_mem_rightElements : x ◇ y ∈ rightElements x := hom_iff_exists_right.2 ⟨_, rfl⟩
@[simp] lemma mul_mem_leftElements : x ◇ y ∈ leftElements y := hom_iff_exists_left.2 ⟨_, rfl⟩

lemma rightElements_eq_range_mul : rightElements x = Set.range (x ◇ ·) := by
  ext z; simp [mem_rightElements_iff_exists]

lemma leftElements_eq_range_mul : leftElements x = Set.range (· ◇ x) := by
  ext z; simp [mem_leftElements_iff_exists]

section

open scoped Classical

noncomputable def width (α : Type*) [CentralMagma α] : ℕ :=
  if h : Nonempty α
    then (rightElements h.some).ncard
    else 0

end

/--
We have an equivalence between the rightElements of any element and the leftElements of any
element.
-/
def rightElements_equiv_leftElements : rightElements x ≃ leftElements y where
  toFun := (⟨· ◇ y, mul_mem_leftElements⟩)
  invFun := (⟨x ◇ ·, mul_mem_rightElements⟩)
  left_inv := by
    rintro ⟨_, ⟨u, rfl⟩⟩
    ext1
    dsimp
    rw [mul_mul_mul_cancel]
  right_inv := by
    rintro ⟨_, ⟨u, rfl⟩⟩
    ext1
    simp

/--
We have an equivalence between the rightElements of any element and the rightElements of any
element.
-/
def rightElements_equiv_rightElements : rightElements x ≃ rightElements y := calc
  rightElements x ≃ leftElements x := rightElements_equiv_leftElements
  _ ≃ rightElements y := rightElements_equiv_leftElements.symm

/--
We have an equivalence between the leftElements of any element and the leftElements of any
element.
-/
def leftElements_equiv_leftElements : leftElements x ≃ leftElements y := calc
  leftElements x ≃ rightElements x := rightElements_equiv_leftElements.symm
  _ ≃ leftElements y := rightElements_equiv_leftElements

lemma Set.ncard_congr' {α β : Type*} {s : Set α} {t : Set β} (e : s ≃ t) : s.ncard = t.ncard := by
  rw [Set.ncard_def, Set.ncard_def, Set.encard_congr e]

@[simp] lemma rightElements_ncard_eq_width : (rightElements x).ncard = width α := by
  rw [width, dif_pos ⟨x⟩, Set.ncard_congr' rightElements_equiv_rightElements]

@[simp] lemma leftElements_ncard_eq_width : (leftElements x).ncard = width α := by
  rw [width, dif_pos ⟨x⟩, Set.ncard_congr' rightElements_equiv_leftElements]

@[simp] lemma univ_filter_to_eq [Fintype α] [DecidableEq α] :
    Finset.univ.filter (x ⟶ ·) = rightElements x := by
  simp [rightElements]

@[simp] lemma univ_filter_from_eq [Fintype α] [DecidableEq α] :
    Finset.univ.filter (· ⟶ x) = leftElements x := by
  simp [leftElements]

lemma rightElements_disjoint {x i j : α} (hi : i ∈ rightElements x) (hj : j ∈ rightElements x)
    (hij : i ≠ j) : Disjoint (rightElements i) (rightElements j) := by
  rw [Set.disjoint_left]
  intro a hai haj
  rw [mem_rightElements_iff_hom] at *
  exact hij (eq_of_homs hi hai hj haj)

lemma rightElements_pairwiseDisjoint {x : α} :
    (rightElements x).PairwiseDisjoint rightElements := by
  intro y hy z hz h
  exact rightElements_disjoint hy hz h

lemma rightElements_cover {x : α} : ⋃ y ∈ rightElements x, rightElements y = Set.univ := by
  ext z
  simp only [Set.mem_iUnion, exists_prop, Set.mem_univ, iff_true]
  use x ◇ z
  simp [mem_rightElements_iff_hom]

@[simp] lemma rightElements_nonempty {x : α} : (rightElements x).Nonempty :=
  ⟨x ◇ x, mul_mem_rightElements⟩

@[simp] lemma width_empty {α : Type*} [IsEmpty α] [CentralMagma α] : width α = 0 := by
  rw [width, dif_neg]
  rwa [not_nonempty_iff]

@[simp] lemma width_pos {α : Type*} [Nonempty α] [Finite α] [CentralMagma α] : 0 < width α := by
  rw [width, dif_pos]
  swap
  · infer_instance
  rw [Set.ncard_pos]
  exact rightElements_nonempty

lemma rightElements_infinite [Infinite α] {x : α} : Set.Infinite (rightElements x) := by
  by_contra hx
  simp only [Set.not_infinite] at hx
  have : 0 < (rightElements x).ncard := by
    rw [Set.ncard_pos hx]
    exact rightElements_nonempty
  have : ∀ y : α, Set.Finite (rightElements y) := fun y => Set.finite_of_ncard_pos (by simpa)
  have : (⋃ y ∈ rightElements x, rightElements y).Finite := Set.Finite.biUnion hx fun i _ => this i
  rw [rightElements_cover, Set.finite_univ_iff] at this
  exact Infinite.not_finite this

@[simp] lemma width_infinite {α : Type*} [Infinite α] [CentralMagma α] : width α = 0 := by
  rw [width, dif_pos]
  swap
  · infer_instance
  rw [Set.Infinite.ncard]
  exact rightElements_infinite

lemma Set.ncard_biUnion {α β : Type*} {s : Set α} {t : α → Set β}
    (h' : Set.PairwiseDisjoint s t)
    (hs : s.Finite := by toFinite_tac)
    (h : ∀ x ∈ s, (t x).Finite) :
    (⋃ x ∈ s, t x).ncard = ∑ x in hs.toFinset, (t x).ncard := by
  induction s, hs using Set.Finite.dinduction_on with
  | H0 => simp
  | H1 =>
      classical
      rename_i a s has hs ih
      simp only [Set.mem_insert_iff, forall_eq_or_imp] at h
      rw [Set.pairwiseDisjoint_insert_of_not_mem has] at h'
      have hd : Disjoint (t a) (⋃ x ∈ s, t x) := by
        rw [Set.disjoint_iUnion₂_right]
        exact h'.2
      simp only [Set.mem_insert_iff, Set.iUnion_iUnion_eq_or_left]
      have : (⋃ x ∈ s, t x).Finite := Set.Finite.biUnion hs h.2
      rw [Set.ncard_union_eq hd h.1 this, Set.Finite.toFinset_insert, Finset.sum_insert,
        ih h'.1 h.2]
      simpa

lemma card_eq_width_mul_width (α : Type*) [CentralMagma α] : Nat.card α = width α * width α := by
  cases' (finite_or_infinite α).symm with hα hα
  · simp
  rcases isEmpty_or_nonempty α with hα | ⟨⟨x⟩⟩
  · simp
  -- have : Nat.card α = Set.ncard (@Set.univ α) := by rw [Set.ncard_univ]
  have : Set.Finite (rightElements x) := by toFinite_tac
  rw [←Set.ncard_univ, ←rightElements_cover (x := x),
    Set.ncard_biUnion rightElements_pairwiseDisjoint]
  simp only [rightElements_ncard_eq_width, Finset.sum_const, smul_eq_mul]
  · rw [←Set.ncard_eq_toFinset_card, rightElements_ncard_eq_width]
  intro y _
  toFinite_tac

lemma ncard_isSquare (α : Type*) [CentralMagma α] : IsSquare (Nat.card α) :=
  ⟨width α, card_eq_width_mul_width α⟩

lemma exists_central_card_iff (n : ℕ) :
    (∃ α : Type*, Nonempty (CentralMagma α) ∧ Nat.card α = n) ↔ IsSquare n := by
  constructor
  · rintro ⟨α, ⟨⟨h⟩, rfl⟩⟩
    exact ncard_isSquare α
  · rintro ⟨n, rfl⟩
    exact exists_central_mul_card _

lemma exists_magma_168_card_iff (n : ℕ) :
    (∃ (G : Type*) (_ : Magma G), Equation168 G ∧ Nat.card G = n) ↔ IsSquare n := by
  constructor
  · rintro ⟨α, h, hα, rfl⟩
    have : CentralMagma α := ⟨fun x y z => (hα _ _ _).symm⟩
    exact ncard_isSquare α
  · rintro ⟨n, rfl⟩
    obtain ⟨G, ⟨hG⟩, hG₂⟩ := exists_central_mul_card n
    exact ⟨G, inferInstance, fun x y z => (central _ _ _).symm, hG₂⟩

universe u

-- equation (11) from [Knuth]
-- Equation4689
def IsNatural (α : Type*) [CentralMagma α] : Prop := ∀ x y z w : α, (x ◇ y) ◇ z = (w ◇ y) ◇ z

lemma IsNatural.eq (h : IsNatural α) {x y z} (w : α) : (x ◇ y) ◇ z = (w ◇ y) ◇ z := h _ _ _ _

lemma IsNatural.op_aux (h : IsNatural α) {x y z : α} : x ◇ (y ◇ z) = x ◇ (y ◇ y) :=
  calc x ◇ (y ◇ z) = x ◇ ((x ◇ (y ◇ z)) ◇ y) := by simp
    _ = x ◇ (((x ◇ y) ◇ (y ◇ z)) ◇ y) := by rw [h.eq]
    _ = x ◇ (y ◇ y) := by rw [central]

-- equation (12) from [Knuth]
-- Equation4357
lemma IsNatural.op (h : IsNatural α) {x y z : α} (w : α) : x ◇ (y ◇ z) = x ◇ (y ◇ w) := by
  rw [h.op_aux, h.op_aux (z := w)]

lemma IsNatural.mop_iff : IsNatural αᵐᵒᵖ ↔ ∀ x y z w : α, x ◇ (y ◇ z) = x ◇ (y ◇ w) :=
  ⟨fun h _ _ _ _ => op_injective (h _ _ _ _), fun h _ _ _ _ => unop_injective (h _ _ _ _)⟩

lemma IsNatural.mop (h : IsNatural α) : IsNatural αᵐᵒᵖ := fun _ _ _ _ => unop_injective (h.op _)

lemma IsNatural.of_mop (h : IsNatural αᵐᵒᵖ) : IsNatural α := fun _ _ _ _ => op_injective (h.op _)

lemma IsNatural_natural {S : Type u} : IsNatural (Natural S) := fun _ _ _ _ => by simp [product_mul]

lemma IsNatural.equiv {α β : Type u} [CentralMagma α] [CentralMagma β] (e : α ≃◇ β)
    (h : IsNatural β) : IsNatural α := fun x y z w =>
  e.injective <| by
    simp only [toEquiv_eq_coe, EquivLike.coe_coe, MagmaHomClass.map_op e]
    exact h _ _ _ _

-- 13 => 1
def CentralMagma_of_single {α : Type*} [Magma α]
    (h : ∀ x y z w : α, (x ◇ ((y ◇ z) ◇ w)) ◇ (z ◇ w) = z) :
    CentralMagma α where
  central := fun y z w =>
  calc (y ◇ z) ◇ (z ◇ w) =
      ((y ◇ ((w ◇ (y ◇ z)) ◇ w)) ◇ ((y ◇ z) ◇ w)) ◇ (z ◇ w) := by rw [h y w (y ◇ z) w]
    _ = z := h _ _ _ _

-- 13 => 14 (in the context of 1)
-- this is a special case of the equation required to be natural
-- equation 4587
lemma special_natural_of_single (h : ∀ x y z w : α, (x ◇ ((y ◇ z) ◇ w)) ◇ (z ◇ w) = z) (x t : α) :
    (x ◇ t) ◇ t = (t ◇ t) ◇ t := by
  simpa using h x (t ◇ (t ◇ t)) ((t ◇ t) ◇ t) (t ◇ t)

def leftPart (x : α) : α := (x ◇ x) ◇ x
def rightPart (x : α) : α := x ◇ (x ◇ x)

@[simp] lemma op_rightPart : op (rightPart x) = leftPart (op x) := rfl
@[simp] lemma op_leftPart : op (leftPart x) = rightPart (op x) := rfl
@[simp] lemma unop_rightPart {x : αᵐᵒᵖ} : unop (rightPart x) = leftPart (unop x) := rfl
@[simp] lemma unop_leftPart {x : αᵐᵒᵖ} : unop (leftPart x) = rightPart (unop x) := rfl

lemma leftPart_mul_rightPart : leftPart x ◇ rightPart x = x := by
  rw [leftPart, rightPart, central]

-- 11 => 16
lemma IsNatural.rightPart_mul_leftPart (h : IsNatural α) {x y : α} :
    rightPart x ◇ leftPart y = x ◇ y := by
  rw [rightPart, h.eq (x ◇ x), leftPart, h.op (y ◇ y), central, central]

lemma eq16_dual (h : ∀ x y : α, rightPart x ◇ leftPart y = x ◇ y) :
    ∀ x y : αᵐᵒᵖ, rightPart x ◇ leftPart y = x ◇ y :=
  fun _ _ => unop_injective <| h _ _

-- 16 => 17
-- 16 => 14
lemma eq14_of_eq16 (h : ∀ x y : α, rightPart x ◇ leftPart y = x ◇ y) (x : α) {y : α} :
    leftPart y = (x ◇ y) ◇ y := by
  rw [←h x y, leftPart]
  simp

-- 16 => 18
lemma eq18_of_eq16 (h : ∀ x y : α, rightPart x ◇ leftPart y = x ◇ y) (x : α) {y : α} :
    rightPart x = x ◇ (x ◇ y) :=
  op_injective <| eq14_of_eq16 (eq16_dual h) _

-- 16 => 19
lemma eq19_of_eq16 (h : ∀ x y : α, rightPart x ◇ leftPart y = x ◇ y) {x y : α} :
    leftPart (x ◇ y) = rightPart x := by
  rw [eq14_of_eq16 h, central (y ◇ x), eq18_of_eq16 h]

-- 16 => 20
lemma eq20_of_eq16 (h : ∀ x y : α, rightPart x ◇ leftPart y = x ◇ y) {x y : α} :
    rightPart (x ◇ y) = leftPart y :=
  op_injective <| eq19_of_eq16 <| eq16_dual h

-- 19 => 20
lemma eq20_of_eq19 (h : ∀ x y : α, leftPart (x ◇ y) = rightPart x) {x y : α} :
    rightPart (x ◇ y) = leftPart y := by
  rw [←h (x ◇ y) (y ◇ x), central]

-- 20 => 19
lemma eq19_of_eq20 (h : ∀ x y : α, rightPart (x ◇ y) = leftPart y) {x y : α} :
    leftPart (x ◇ y) = rightPart x := by
  rw [←h (y ◇ x) (x ◇ y), central]

-- 20 => 22
lemma eq16_of_eq20_auxl (h : ∀ x y : α, rightPart (x ◇ y) = leftPart y) {x y : α} :
    x ◇ leftPart y = x ◇ y := by
  rw [←h x y, rightPart]
  simp

-- 19 => 23
lemma eq16_of_eq19_auxr (h : ∀ x y : α, leftPart (x ◇ y) = rightPart x) {x y : α} :
    rightPart x ◇ y = x ◇ y := by
  rw [←h x y, leftPart]
  simp

-- 22,23 => 16
lemma eq16_of_eq22_of_eq23
    (h22 : ∀ x y : α, x ◇ leftPart y = x ◇ y)
    (h23 : ∀ x y : α, rightPart x ◇ y = x ◇ y)
    {x y : α} :
    rightPart x ◇ leftPart y = x ◇ y := by
  rw [h23, h22]

lemma leftPart_idem (h : ∀ x y : α, rightPart x ◇ leftPart y = x ◇ y) :
    leftPart x ◇ leftPart x = leftPart x :=
  calc leftPart x ◇ leftPart x = rightPart (x ◇ x) ◇ leftPart x := by rw [eq20_of_eq16 h]
    _ = _ := h _ _

lemma rightPart_idem (h : ∀ x y : α, rightPart x ◇ leftPart y = x ◇ y) :
    rightPart x ◇ rightPart x = rightPart x :=
  calc rightPart x ◇ rightPart x = _ := by rw [eq19_of_eq16 h]
    _ = x ◇ (x ◇ x) := h _ _

lemma unique_rep (h : ∀ x y : α, rightPart x ◇ leftPart y = x ◇ y)
    {x u v : α} (hx : x = u ◇ v) (hu : u ◇ u = u) (hv : v ◇ v = v) :
    leftPart x = u ∧ rightPart x = v := by
  rw [hx, eq19_of_eq16 h, eq20_of_eq16 h, rightPart, hu, hu, leftPart, hv, hv]
  simp

def equivalence (h : ∀ x y : α, rightPart x ◇ leftPart y = x ◇ y) :
    α ≃◇ Natural {x : α // x ◇ x = x} where
  toFun := fun x => ⟨⟨leftPart x, leftPart_idem h⟩, ⟨rightPart x, rightPart_idem h⟩⟩
  invFun := fun ⟨u, v⟩ => u ◇ v
  left_inv := fun x => leftPart_mul_rightPart
  right_inv := fun ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ => by
    simp only [Prod.mk.injEq, Subtype.mk.injEq, Natural]
    exact unique_rep h rfl hu hv
  map_op' := by
    intro x y
    simp only
    rw [product_mul, Prod.mk.injEq]
    simp only [Subtype.mk.injEq]
    rw [eq19_of_eq16 h, eq20_of_eq16 h]
    simp

lemma eq22_iff_eq14 :
    x ◇ leftPart y = x ◇ y ↔ (x ◇ y) ◇ y = leftPart y := by
  constructor
  · intro h
    rw [←h, leftPart, mul_mul_mul_cancel']
  · intro h
    rw [←h, mul_mul_mul_cancel]

lemma eq23_iff_hom : rightPart x ◇ y = x ◇ y ↔ (rightPart x ⟶ x ◇ y) := by
  constructor
  · intro h
    rw [←h]
    exact to_mul
  · intro h
    exact mul_eq_of_hom h from_mul

lemma eq23_iff_eq18 :
    rightPart x ◇ y = x ◇ y ↔ x ◇ (x ◇ y) = rightPart x := by
  constructor
  · intro h
    rw [←h, rightPart, mul_mul_mul_cancel]
  · intro h
    rw [←h, mul_mul_mul_cancel']

-- 23 => 18
-- 23 => E
lemma eq18_of_eq23 (y : α) (h : ∀ x y : α, rightPart x ◇ y = x ◇ y) :
    x ◇ (x ◇ y) = rightPart x :=
  eq23_iff_eq18.1 (h x y)

lemma rightPart_idem_of_eq23 (h : ∀ x y : α, rightPart x ◇ y = x ◇ y) :
    rightPart x ◇ rightPart x = rightPart x := by
  rw [idempotent_iff_hom_self]
  exact eq23_iff_hom.1 (h _ _)

-- 23 => D
lemma eqD_of_eq23 (h : ∀ x y : α, rightPart x ◇ y = x ◇ y) :
    rightPart (rightPart x) = rightPart x := by
  rw [rightPart, rightPart_idem_of_eq23 h, rightPart_idem_of_eq23 h]

-- 23 => F
lemma eqF_of_eq23 (h : ∀ x y : α, rightPart x ◇ y = x ◇ y) :
    rightPart (x ◇ y) = (x ◇ y) ◇ y := by
  rw [←eq18_of_eq23 (y ◇ y) h, central]

-- 23 => G
lemma eqG_of_eq23 (h : ∀ x y : α, rightPart x ◇ y = x ◇ y) :
    rightPart (x ◇ x) = leftPart x := by
  rw [eqF_of_eq23 h, leftPart]

-- 23 => K
lemma eqK_of_eq23 (h : ∀ x y : α, rightPart x ◇ y = x ◇ y) :
    rightPart (x ◇ rightPart y) = rightPart y :=
  calc rightPart (x ◇ rightPart y) = (x ◇ rightPart y) ◇ rightPart y := eqF_of_eq23 h
    _ = (x ◇ rightPart y) ◇ rightPart (rightPart y) := by rw [eqD_of_eq23 h]
    _ = rightPart y := by rw [rightPart, rightPart, central]

-- 23 => L
lemma eqL_of_eq23 (h : ∀ x y : α, rightPart x ◇ y = x ◇ y) :
    (x ◇ rightPart y) ◇ z = y ◇ z := by
  rw [←h, eqK_of_eq23 h, h]

-- 23 => 22
lemma eq22_of_eq23 (h : ∀ x y : α, rightPart x ◇ y = x ◇ y) :
    x ◇ leftPart y = x ◇ y :=
  calc x ◇ leftPart y = x ◇ rightPart (y ◇ y) := by rw [eqG_of_eq23 h]
    _ = x ◇ rightPart (rightPart (y ◇ y)) := by rw [eqD_of_eq23 h]
    _ = x ◇ rightPart (leftPart y) := by rw [eqG_of_eq23 h]
    _ = x ◇ ((x ◇ rightPart (leftPart y)) ◇ rightPart y) := mul_mul_mul_cancel.symm
    _ = x ◇ (leftPart y ◇ rightPart y) := by rw [eqL_of_eq23 h]
    _ = x ◇ y := by rw [leftPart_mul_rightPart]

lemma eq23_of_eq22 (h : ∀ x y : α, x ◇ leftPart y = x ◇ y) :
    rightPart x ◇ y = x ◇ y :=
  op_injective <| eq22_of_eq23 fun _ _ => unop_injective <| h _ _

open List in

lemma tfae_natural_aux (α : Type u) [CentralMagma α] :
    TFAE
      [IsNatural α, -- eq 11
       IsNatural αᵐᵒᵖ,
       ∃ S : Type u, Nonempty (α ≃◇ Natural S),
       ∀ x y z w : α, x ◇ (y ◇ z) = x ◇ (y ◇ w), -- eq 12
       ∀ x y : α, leftPart y = (x ◇ y) ◇ y, -- eq 14, eq 17
       ∀ x y : α, rightPart x ◇ leftPart y = x ◇ y, -- eq 16
       ∀ x y : α, rightPart x = x ◇ (x ◇ y), -- eq 18
       ∀ x y : α, leftPart (x ◇ y) = rightPart x, -- eq 19
       ∀ x y : α, rightPart (x ◇ y) = leftPart y, -- eq 20
       ∀ x y : α, x ◇ leftPart y = x ◇ y, -- eq 22
       ∀ x y : α, rightPart x ◇ y = x ◇ y, -- eq 23
       ] := by
  tfae_have 1 → 2
  · exact IsNatural.mop
  tfae_have 2 → 1
  · exact IsNatural.of_mop
  tfae_have 2 ↔ 4
  · rw [IsNatural.mop_iff]
  tfae_have 3 → 1
  · rintro ⟨S, ⟨e⟩⟩
    exact IsNatural_natural.equiv e
  tfae_have 1 → 6
  · exact IsNatural.rightPart_mul_leftPart
  tfae_have 6 → 3
  · intro h
    exact ⟨_, ⟨equivalence h⟩⟩
  tfae_have 6 → 8
  · exact eq19_of_eq16
  tfae_have 6 → 9
  · exact eq20_of_eq16
  tfae_have 8 → 9
  · intro h x y
    exact eq20_of_eq19 h
  tfae_have 9 → 8
  · intro h x y
    exact eq19_of_eq20 h
  tfae_have 10 → 11
  · intro h x y
    exact eq23_of_eq22 h
  tfae_have 11 → 10
  · intro h x y
    exact eq22_of_eq23 h
  tfae_have 11 ↔ 7
  · simp_rw [eq23_iff_eq18, eq_comm]
  tfae_have 11 → 6
  · intro h x y
    exact eq16_of_eq22_of_eq23 (tfae_11_to_10 h) h
  tfae_have 9 → 10
  · intro h x y
    exact eq16_of_eq20_auxl h
  tfae_have 10 ↔ 5
  · simp_rw [eq22_iff_eq14, eq_comm]
  tfae_finish

end CentralMagma

namespace FreeMagma

inductive Reduction : FreeMagma α → FreeMagma α → Prop
  | left {x y z} : Reduction x y → Reduction (.Fork x z) (.Fork y z)
  | right {x y z} : Reduction x y → Reduction (.Fork z x) (.Fork z y)
  | midCancel {x y z} : Reduction (.Fork (.Fork x y) (.Fork y z)) y
  | leftCancel {x y z} : Reduction (.Fork x (.Fork (.Fork x y) z)) (.Fork x y)
  | rightCancel {x y z} : Reduction (.Fork (.Fork x (.Fork y z)) z) (.Fork y z)

open Relation

lemma Reduction.mulOp : {x y : FreeMagma α} → Reduction x y → Reduction x.op y.op
  | _, _, .left h => .right h.mulOp
  | _, _, .right h => .left h.mulOp
  | _, _, .midCancel => .midCancel
  | _, _, .leftCancel => .rightCancel
  | _, _, .rightCancel => .leftCancel

lemma _root_.Relation.ReflTransGen.op : {x y : FreeMagma α} →
    ReflTransGen Reduction x y → ReflTransGen Reduction x.op y.op :=
  ReflTransGen.lift _ fun _ _ => Reduction.mulOp

theorem newman {r : α → α → Prop} (hr : WellFounded (flip r))
    (hrc : ∀ a b c, r a b → r a c → ∃ d, ReflTransGen r b d ∧ ReflTransGen r c d) (x y z) :
    ReflTransGen r x y → ReflTransGen r x z → Join (ReflTransGen r) y z := by
  induction x using hr.induction generalizing y z with
  | h x ih =>
      intro hxy hxz
      rcases eq_or_ne x y with rfl | hxy'
      case inl => exact ⟨_, hxz, .refl⟩
      rcases eq_or_ne x z with rfl | hxz'
      case inl => exact ⟨_, .refl, hxy⟩
      rw [ReflTransGen.cases_head_iff] at hxy hxz
      obtain ⟨y₁, hxy₁, hy₁y⟩ := hxy.resolve_left hxy'
      obtain ⟨z₁, hxz₁, hz₁z⟩ := hxz.resolve_left hxz'
      obtain ⟨u, hy₁u, hz₁u⟩ := hrc _ _ _ hxy₁ hxz₁
      obtain ⟨v, hyv, huv⟩ := ih y₁ hxy₁ _ _ hy₁y hy₁u
      obtain ⟨w, hzw, hvw⟩ := ih z₁ hxz₁ z v hz₁z (hz₁u.trans huv)
      exact ⟨w, hyv.trans hvw, hzw⟩

theorem locally_confluent_midCancel {x y z u : FreeMagma α} :
    Reduction (.Fork (.Fork x y) (.Fork y z)) u →
      ∃ w, ReflTransGen Reduction y w ∧ ReflTransGen Reduction u w
  | .midCancel => ⟨_, .refl, .refl⟩
  | .right (.left h) => ⟨_, .single h, .tail (.single (.left (.right h))) .midCancel⟩
  | .right (.right h) => ⟨_, .refl, .single .midCancel⟩
  | .right .midCancel => ⟨_, .refl, .single .rightCancel⟩
  | .right .leftCancel => ⟨_, .refl, .single .midCancel⟩
  | .right .rightCancel => ⟨_, .refl, .single .rightCancel⟩
  | .left (.left h) => ⟨_, .refl, .single .midCancel⟩
  | .left (.right h) => ⟨_, .single h, .tail (.single (.right (.left h))) .midCancel⟩
  | .left .midCancel => ⟨_, .refl, .single .leftCancel⟩
  | .left .leftCancel => ⟨_, .refl, .single .leftCancel⟩
  | .left .rightCancel => ⟨_, .refl, .single .midCancel⟩

theorem locally_confluent_leftCancel {x y z u : FreeMagma α} :
    Reduction (.Fork x (.Fork (.Fork x y) z)) u →
      ∃ w, ReflTransGen Reduction (.Fork x y) w ∧ ReflTransGen Reduction u w := by
  intro h
  cases h with
  | leftCancel => exact ⟨_, .refl, .refl⟩
  | left h =>
      cases h with
      | left h => exact ⟨_, .single h.left.left, .tail (.single h.left.left.left.right) .leftCancel⟩
      | right h =>
          exact ⟨_, .single h.right.left, .tail (.single h.right.left.left.right) .leftCancel⟩
      | midCancel =>
          exact ⟨_, .single (.left .midCancel),
            .tail (.single Reduction.midCancel.left.left.right) .leftCancel⟩
      | leftCancel =>
          exact ⟨_, .single (.left .leftCancel),
            .tail (.single (.right (.left (.left .leftCancel)))) .leftCancel⟩
      | rightCancel =>
          exact ⟨_, .single (.left .rightCancel),
            .tail (.single (.right (.left (.left .rightCancel)))) .leftCancel⟩
  | right h =>
      cases h with
      | left h =>
          cases h with
          | left h => exact ⟨_, .single (.left h), .tail (.single (.left h)) .leftCancel⟩
          | right h => exact ⟨_, .single (.right h), .single .leftCancel⟩
          | midCancel => exact ⟨_, .single .midCancel, .single .midCancel⟩
          | leftCancel => exact ⟨_, .single .leftCancel, .single .leftCancel⟩
          | rightCancel => exact ⟨_, .single .rightCancel, .single .midCancel⟩
      | right h => exact ⟨_, .refl, .single .leftCancel⟩
      | rightCancel => exact ⟨_, .refl, .refl⟩
      | midCancel => exact ⟨_, .refl, .refl⟩
      | leftCancel => exact ⟨_, .refl, .single .leftCancel⟩

theorem locally_confluent_rightCancel {x y z u : FreeMagma α} :
    Reduction (.Fork (.Fork x (.Fork y z)) z) u →
      ∃ w, ReflTransGen Reduction (.Fork y z) w ∧ ReflTransGen Reduction u w := by
  intro h
  obtain ⟨w, hw1, hw2⟩ := locally_confluent_leftCancel h.mulOp
  refine ⟨w.op, ?_, ?_⟩
  · simpa [FreeMagma.op] using hw1.op
  · simpa using hw2.op

lemma _root_.Relation.ReflTransGen.left {z} : {x y : FreeMagma α} →
    ReflTransGen Reduction x y → ReflTransGen Reduction (.Fork x z) (.Fork y z) :=
  ReflTransGen.lift (FreeMagma.Fork · z) fun _ _ h => h.left

lemma _root_.Relation.ReflTransGen.right {z} : {x y : FreeMagma α} →
    ReflTransGen Reduction x y → ReflTransGen Reduction (.Fork z x) (.Fork z y) :=
  ReflTransGen.lift (FreeMagma.Fork z) fun _ _ h => h.right

lemma _root_.Relation.TransGen.left {z} : {x y : FreeMagma α} →
    TransGen Reduction x y → TransGen Reduction (.Fork x z) (.Fork y z) :=
  TransGen.lift (FreeMagma.Fork · z) fun _ _ h => h.left

lemma _root_.Relation.TransGen.right {z} : {x y : FreeMagma α} →
    TransGen Reduction x y → TransGen Reduction (.Fork z x) (.Fork z y) :=
  TransGen.lift (FreeMagma.Fork z) fun _ _ h => h.right

theorem locally_confluent : {x y z : FreeMagma α} → Reduction x y → Reduction x z →
    ∃ w, ReflTransGen Reduction y w ∧ ReflTransGen Reduction z w
  | _, _, _, .midCancel, h => locally_confluent_midCancel h
  | _, _, _, .leftCancel, h => locally_confluent_leftCancel h
  | _, _, _, .rightCancel, h => locally_confluent_rightCancel h
  | _, _, _, h, .midCancel => let ⟨w, hw1, hw2⟩ := locally_confluent_midCancel h; ⟨w, hw2, hw1⟩
  | _, _, _, h, .leftCancel => let ⟨w, hw1, hw2⟩ := locally_confluent_leftCancel h; ⟨w, hw2, hw1⟩
  | _, _, _, h, .rightCancel => let ⟨w, hw1, hw2⟩ := locally_confluent_rightCancel h; ⟨w, hw2, hw1⟩
  | _, _, _, .left h, .left h' =>
      let ⟨_, hw1, hw2⟩ := locally_confluent h h';
      ⟨_, hw1.left, hw2.left⟩
  | _, _, _, .left h, .right h' => ⟨_, .single h'.right, .single h.left⟩
  | _, _, _, .right h, .left h' => ⟨_, .single h'.left, .single h.right⟩
  | _, _, _, .right h, .right h' =>
      let ⟨_, hw1, hw2⟩ := locally_confluent h h';
      ⟨_, hw1.right, hw2.right⟩

-- count the number of muls
def size : FreeMagma α → ℕ
  | .Leaf _ => 0
  | .Fork x y => 1 + size x + size y

lemma smaller {x y : FreeMagma α} : Reduction x y → size y < size x
  | .left h => by simpa [size] using smaller h
  | .right h => by simpa [size] using smaller h
  | .midCancel => by simp [size]; omega
  | .leftCancel => by simp [size]; omega
  | .rightCancel => by simp [size]; omega

lemma smaller' {x y : FreeMagma α} (h : ReflTransGen Reduction x y) : size y ≤ size x := by
  induction h
  case refl => exact le_rfl
  case tail h ih => exact ih.trans' (smaller h).le

lemma wellFounded_flip_reduction : WellFounded (flip (@Reduction α)) :=
  wellFounded_lt.onFun.mono fun _ _ => smaller

theorem confluent {x y z : FreeMagma α} :
    ReflTransGen Reduction x y → ReflTransGen Reduction x z →
      Join (ReflTransGen Reduction) y z := by
  apply newman _ (fun a b c => locally_confluent) _ _ _
  exact wellFounded_lt.onFun.mono fun _ _ => smaller

lemma exists_reduction (x : FreeMagma α) :
    ∃ y, ReflTransGen Reduction x y ∧ ∀ z, ¬ Reduction y z := by
  induction x using wellFounded_flip_reduction.induction with
  | h x ih =>
      by_cases ∃ y, Reduction x y
      case pos h =>
        obtain ⟨y, hy⟩ := h
        obtain ⟨z, hz⟩ := ih y hy
        exact ⟨z, .head hy hz.1, hz.2⟩
      case neg h =>
        simp only [not_exists] at h
        exact ⟨x, .refl, h⟩

noncomputable def reduce (x : FreeMagma α) := (exists_reduction x).choose

lemma reduce_reduced {x : FreeMagma α} : ReflTransGen Reduction x (reduce x) :=
  (exists_reduction x).choose_spec.1

lemma not_reduction_reduce {x : FreeMagma α} : ∀ y, ¬ Reduction (reduce x) y :=
  (exists_reduction x).choose_spec.2

lemma reduce_fully_reduced' (x : FreeMagma α) : ∀ y, ¬ TransGen Reduction (reduce x) y := by
  intro y hy
  rw [TransGen.head'_iff] at hy
  obtain ⟨z, hz, -⟩ := hy
  exact not_reduction_reduce z hz

lemma reduce_fully_reduced'' {x y : FreeMagma α} (h : ReflTransGen Reduction (reduce x) y) :
    x.reduce = y := by
  rw [reflTransGen_iff_eq_or_transGen] at h
  exact (h.resolve_right (reduce_fully_reduced' x y)).symm

lemma reduce_fully_reduced''' {x : FreeMagma α} (hx : ∀ y, ¬ Reduction x y) :
    x.reduce = x := by
  have h : ReflTransGen Reduction x x.reduce := reduce_reduced
  rw [ReflTransGen.cases_head_iff] at h
  exact (h.resolve_right fun ⟨i, hi, _⟩ => hx _ hi).symm

lemma reduce_eq_reduced {x y : FreeMagma α} (hxy : ReflTransGen Reduction x y) :
    x.reduce = y.reduce := by
  obtain ⟨z, hzx, hzy⟩ := confluent reduce_reduced hxy
  cases reduce_fully_reduced'' hzx
  obtain ⟨w, hxw, hyw⟩ := confluent reduce_reduced hzy
  cases reduce_fully_reduced'' hxw
  exact reduce_fully_reduced'' hyw

lemma reduce_eq {x y} (z : FreeMagma α)
    (hzx : ReflTransGen Reduction z x) (hzy : ReflTransGen Reduction z y) :
    x.reduce = y.reduce := by
  obtain ⟨w, hwx, hwy⟩ := confluent hzx hzy
  rw [reduce_eq_reduced hwx, reduce_eq_reduced hwy]

lemma reduce_mul (x y : FreeMagma α) :
    (FreeMagma.Fork x.reduce y.reduce).reduce = (FreeMagma.Fork x y).reduce :=
  reduce_eq (x.Fork y) (.trans (.right reduce_reduced) (.left reduce_reduced)) .refl

/--
We define the free central magma on `α` as the elements of the free magma which do not have a
reduction using one of the rules.
Note that the rules are not just 168, but also X and Y
TODO: find the numbers for X and Y
-/
def FreelyCentral.{u} (α : Type u) : Type u := {x : FreeMagma α // ∀ y, ¬ Reduction x y}

noncomputable instance : Magma (FreelyCentral α) where
  op x y := ⟨reduce (x.1.Fork y.1), not_reduction_reduce⟩

lemma mul_def (x y : FreelyCentral α) : x ◇ y = ⟨reduce (x.1.Fork y.1), not_reduction_reduce⟩ := rfl
lemma mul_mk {x y : FreeMagma α} (hx hy) :
    (⟨x, hx⟩ ◇ ⟨y, hy⟩ : FreelyCentral α) = ⟨reduce (x.Fork y), not_reduction_reduce⟩ := rfl

noncomputable instance : CentralMagma (FreelyCentral α) where
  central := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
    rw [mul_mk, mul_mk, mul_mk]
    refine Subtype.ext ?_
    dsimp
    rw [reduce_mul]
    have : y.reduce = y := reduce_fully_reduced''' hy
    conv_rhs => rw [← this]
    exact reduce_eq_reduced (.single .midCancel)

lemma mul_idem_aux {x y z : FreeMagma α} (h : ∀ w, ¬ Reduction (x.Fork y) w) :
    Reduction ((x.Fork y).Fork (x.Fork y)) z → x = y
  | .left h' => (h _ h').elim
  | .right h' => (h _ h').elim
  | .midCancel => rfl

lemma var_reduce {x : α} {y : FreeMagma α} : ¬ Reduction (Leaf x) y := nofun
lemma var_var_reduce {x : α} (y : FreeMagma α) : ¬ Reduction ((Leaf x).Fork (Leaf x)) y := nofun

lemma no_idem {x : FreelyCentral α} : x ◇ x ≠ x := by
  rcases x with ⟨x, hx⟩
  rw [mul_mk, ne_eq, Subtype.ext_iff, Subtype.coe_mk, Subtype.coe_mk]
  cases x with
  | Leaf a =>
      rw [reduce_fully_reduced''' var_var_reduce]
      nofun
  | Fork x y =>
      by_cases ∀ z, ¬ Reduction ((x.Fork y).Fork (x.Fork y)) z
      case pos h =>
        rw [reduce_fully_reduced''' h]
        nofun
      case neg h =>
        push_neg at h
        obtain ⟨z, hz⟩ := h
        cases mul_idem_aux hx hz
        intro h
        have : ((x.Fork x).Fork (x.Fork x)).reduce = x.reduce := by
          apply reduce_eq_reduced _
          exact .single .midCancel
        have : x.Fork x = x.reduce := by rwa [← h]
        have : ReflTransGen Reduction x (x.Fork x) := by
          rw [this]
          exact reduce_reduced
        have' := smaller' this
        simp [size] at this

/-- There is a magma satisfying equation 168 which contains no idempotents. -/
theorem no_idempotents : ∃ (G : Type) (_ : Magma G), Equation168 G ∧ ∀ x : G, x ◇ x ≠ x := by
  refine ⟨FreelyCentral Unit, inferInstance, fun x y z => (CentralMagma.central _ _ _).symm, ?_⟩
  intro x
  exact no_idem
