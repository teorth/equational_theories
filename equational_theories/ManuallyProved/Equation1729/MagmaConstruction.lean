import Mathlib.Order.WithBot

import equational_theories.FreshGenerator
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.ManuallyProved.Equation1729.SmallMagma

namespace Eq1729

instance rel : Setoid N := {
  r := fun x y => ∃ n : ℤ, y = x * (e 0)^n
  iseqv := by
    constructor
    . intro x
      use 0
      simp only [zpow_zero, mul_one]
    . intro x y ⟨ n, h1 ⟩
      use -n
      rw [h1, mul_assoc, ←zpow_add, add_neg_cancel, zpow_zero, mul_one]
    . intro x y z ⟨ n, h1 ⟩ ⟨ m, h2 ⟩
      use n+m
      rw [h2, h1, mul_assoc, zpow_add]
}

lemma rel_iff (x y:N): x ≈ y ↔ ∃ n : ℤ, y = x * (e 0)^n := by rfl

lemma rel_def {x y:N} (h: x ≈ y) : ∃ n : ℤ, y = x * (e 0)^n := (rel_iff x y).mp h

lemma rel_of_mul (x:N) (n:ℤ) : x ≈ x * (e 0)^n := by
  use n

/-- `fill D` is the set of elements of the form (e 0)^n x with x in D and n an integer. -/

def fill (D: Finset N) : Set N := { y | ∃ x, x ≈ y ∧ x ∈ D }

@[simp]
lemma fill_empty : fill Finset.empty = ∅ := by
  ext y
  simp [fill, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
  intro _ _
  exact Finset.not_mem_empty _

lemma fill_mono {D₁ D₂ : Finset N} (h : D₁ ⊆ D₂) : fill D₁ ⊆ fill D₂ := by
  intro y hy
  rcases hy with ⟨x, hx, hD⟩
  exact ⟨x, hx, h hD⟩

lemma fill_invar (D: Finset N) {x y : N} (h : x ≈ y) : x ∈ fill D ↔ y ∈ fill D := by
  constructor
  . intro h
    simp only [fill, Set.mem_setOf_eq] at h ⊢
    obtain ⟨ z, hz, hD ⟩ := h
    exact ⟨ z, Setoid.trans hz h, hD ⟩
  intro h
  simp only [fill, Set.mem_setOf_eq] at h ⊢
  obtain ⟨ z, hz, hD ⟩ := h
  exact ⟨ z, Setoid.trans hz (Setoid.symm h), hD ⟩

lemma fill_invar' (D: Finset N) {x:N} (hx: x ∈ fill D) (n:ℤ) : x * (e 0)^n ∈ fill D := (fill_invar D (rel_of_mul x n)).mp hx

lemma subset_fill (D: Finset N) : D.toSet ⊆ fill D := by
  intro x hx
  simp only [fill, Set.mem_setOf_eq]
  exact ⟨ x, Setoid.refl x, hx ⟩

abbrev axiom_i'' (L₀' : N → N) (Predom : Finset N) := ∀ (x y : N) (_: x ∈ Predom) (_ : L₀' x = y) (n:ℤ), y ∈ fill Predom ∧ L₀' (x * (e 0)^n) = y * (e 0)^n ∧ L₀' (y * (e 0)^n) = x * (e 0)^(n-1)

class PartialSolution where
  L₀' : N → N
  op : N → N → M
  S' : N → SM
  I : Finset (N × N × N)
  Predom_L₀' : Finset N
  Dom_op : Finset (N × N)
  Dom_S' : Finset N
  axiom_i'' : axiom_i'' L₀' Predom_L₀'
  axiom_S (x y : N) (h : x ∈ Dom_S') (h' : y ≤ x) : y ∈ Dom_S'
  axiom_iii'' (x y : N) (a : SM) (hx: x ∈ Dom_S') (hy: y ∈ Dom_S') (h: R' a x = y) : R' (S (a - S' x)) y ∈ fill Predom_L₀' ∧ (R' (S (S' y)) $ (R' (a - S' x)).symm $ L₀' $ R' (S (a - S' x)) y ) ∈ fill Predom_L₀' ∧ ((R' (S' y)).symm $ L₀' $ R' (S (S' y)) $ (R' (a - S' x)).symm $ L₀' $ R' (S (a - S' x)) y ) = x
  axiom_iv'' (x : N) (h : x ∈ Dom_S') : R' (S (S' x)) x ∈ fill Predom_L₀' ∧ (R' (S (S' x)) $ (R' (S' x)).symm $ L₀' $ R' (S (S' x)) x) ∈ fill Predom_L₀' ∧ ((R' (S' x)).symm $ L₀' $ R' (S (S' x)) $ (R' (S' x)).symm $ L₀' $ R' (S (S' x)) x) = x
  axiom_v'' (x : N) (h : (x,x) ∈ Dom_op) : x ∈ Dom_S' ∧ op x x = Sum.inl (S' x)
  axiom_vi'' (y : N) (a : SM) (h: (R' a y, y) ∈ Dom_op) : y ∈ Dom_S' ∧ op (R' a y) y = Sum.inl ( a - S' y )
  axiom_vii'' (x y : N) (h : x ≠ y) (h' : ∀ a : SM, x ≠ R' a y) (hop: (x,y) ∈ Dom_op) : ∃ z : N, op x y = Sum.inr z ∧ ((x,y,z) ∈ I ∧ ((z,x) ∈ Dom_op ∧ (R' 0 $ R' (S' x) $ y) ∈ fill Predom_L₀' ∧ op z x = Sum.inr ((R' (S (S' x))).symm $ L₀' $ R' 0 $ R' (S' x) $ y)))
  axiom_P (x y z : N) (h: (x,y,z) ∈ I) : x ∉ Dom_S' ∧ (z,x) ∉ Dom_op ∧ z ≠ x ∧ (∀ a : SM, z ≠ R' a x)

/-- Not sure if this is the canonical way to proceed, but in order to impose a partial order on PartialSolution I had to first define the LE instance. -/
instance PartialSolution_LE : LE PartialSolution  := {
  le := by
    intro sol1 sol2
    exact sol1.Predom_L₀' ⊆ sol2.Predom_L₀' ∧ sol1.Dom_op ⊆ sol2.Dom_op ∧ sol1.Dom_S' ⊆ sol2.Dom_S' ∧ (∀ x, x ∈ fill sol1.Predom_L₀' → sol1.L₀' x = sol2.L₀' x) ∧ (∀ z ∈ sol1.Dom_op, sol1.op z.1 z.2 = sol2.op z.1 z.2) ∧ (∀ x ∈ sol1.Dom_S', sol1.S' x = sol2.S' x)
}

lemma PartialSolution_refl (sol : PartialSolution) : sol ≤ sol := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try {exact fun _ a ↦ a} <;> try {exact fun _ _ ↦ rfl}

/-- Impose a preorder on solutions using the notion of an extension. -/
instance PartialSolution_order : Preorder PartialSolution  := {
  le := PartialSolution_LE.le
  le_refl := PartialSolution_refl
  le_trans := by
    intro sol1 sol2 sol3 h h'
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_⟩
    . exact h.1.trans h'.1
    . exact h.2.1.trans h'.2.1
    . exact h.2.2.1.trans h'.2.2.1
    . intro x hx
      rw [h.2.2.2.1 x hx, h'.2.2.2.1 x (fill_mono h.1 hx)]
    . intro z hz
      rw [h.2.2.2.2.1 z hz, h'.2.2.2.2.1 z (h.2.1 hz)]
    intro x hx
    rw [h.2.2.2.2.2 x hx, h'.2.2.2.2.2 x (h.2.2.1 hx)]
}

/-- The trivial partial solution. -/
def TrivialPartialSolution : PartialSolution := {
  L₀' := fun _ ↦ 1
  op := fun _ ↦ fun _ ↦ Sum.inl 0
  S' := fun _ ↦ 0
  I := Finset.empty
  Predom_L₀' := Finset.empty
  Dom_op := Finset.empty
  Dom_S' := Finset.empty
  axiom_i'' := by
    intro _ _ h
    contrapose! h
    exact Finset.not_mem_empty _
  axiom_S := by
    intro _ _ h
    contrapose! h
    exact Finset.not_mem_empty _
  axiom_iii'' := by
    intro _ _ _ h
    contrapose! h
    exact Finset.not_mem_empty _
  axiom_iv'' := by
    intro _ h
    contrapose! h
    exact Finset.not_mem_empty _
  axiom_v'' := by
    intro _ h
    contrapose! h
    exact Finset.not_mem_empty _
  axiom_vi'' := by
    intro _ _ h
    contrapose! h
    exact Finset.not_mem_empty _
  axiom_vii'' := by
    intro _ _ _ _ h
    contrapose! h
    exact Finset.not_mem_empty _
  axiom_P := by
    intro _ _ _ h
    contrapose! h
    exact Finset.not_mem_empty _
}

-- for Mathlib?
noncomputable abbrev Set.choose {α: Type} {S: Set α} {P: α → Prop} (h: ∃ s ∈ S, P s) : S := ⟨ _, (Classical.choose_spec h).1 ⟩

-- for Mathlib?
lemma Set.choose_spec {α: Type} {S: Set α} {P: α → Prop} (h: ∃ s ∈ S, P s) : P (Set.choose h) := (Classical.choose_spec h).2

-- for Mathlib?
lemma IsChain.IsDirected {α: Type} [Preorder α] {s: Set α} (h: IsChain (fun x y ↦ x ≤ y) s) [Nonempty s] : IsDirected s (fun x y ↦ x ≤ y) := by
  rw [← directedOn_univ_iff]
  convert (directedOn_image (s := Set.univ) (f := Subtype.val) (r := fun x y ↦ x ≤ y)).mp _
  convert IsChain.directedOn h
  exact Subtype.coe_image_univ s

lemma use_chain {sols : Set PartialSolution} (hchain: IsChain (fun (sol1 sol2 : PartialSolution) => sol1 ≤ sol2) sols ) (hnon: Nonempty sols) (htotal_L₀' : ∀ x : N, ∃ sol ∈ sols, x ∈ fill sol.Predom_L₀') (htotal_S' : ∀ x : N, ∃ sol ∈ sols, x ∈ sol.Dom_S') (htotal_op : ∀ (x y : N), ∃ sol ∈ sols, (x,y) ∈ sol.Dom_op) : ∃ (G: Type) (_: Magma G), Equation1729 G ∧ ¬ Equation817 G := by
  let f := Filter.atTop (α := sols)
  have fnon : f.NeBot := Filter.atTop_neBot_iff.mpr ⟨ hnon, IsChain.IsDirected hchain ⟩

  let S' (x:N) := (Set.choose (htotal_S' x)).1.S' x
  have S'_lim (x:N) : ∀ᶠ sol in f, x ∈ sol.1.Dom_S' ∧ sol.1.S' x = S' x := by
    set sol := Set.choose (htotal_S' x)
    set sol_spec := Set.choose_spec (htotal_S' x)
    apply Filter.Eventually.mono (Filter.eventually_ge_atTop sol) _
    intro _ h
    exact ⟨ h.2.2.1 sol_spec, (h.2.2.2.2.2 x sol_spec).symm ⟩
  let op (x y:N) := (Set.choose (htotal_op x y)).1.op x y
  have op_lim (x y:N) : ∀ᶠ sol in f, (x,y) ∈ sol.1.Dom_op ∧ sol.1.op x y = op x y := by
    set sol := Set.choose (htotal_op x y)
    set sol_spec := Set.choose_spec (htotal_op x y)
    apply Filter.Eventually.mono (Filter.eventually_ge_atTop sol) _
    intro _ h
    exact ⟨h.2.1 sol_spec, (h.2.2.2.2.1 (x,y) sol_spec).symm ⟩
  classical -- didn't want to deal with a Decidable issue
  let L₀' (x:N) := (Set.choose (htotal_L₀' x)).1.L₀' x
  have L₀'_lim (x:N) : ∀ᶠ sol in f, x ∈ fill sol.1.Predom_L₀' ∧ sol.1.L₀' x = L₀' x := by
    set sol := Set.choose (htotal_L₀' x)
    set sol_spec := Set.choose_spec (htotal_L₀' x)
    apply Filter.Eventually.mono (Filter.eventually_ge_atTop sol) _
    intro _ h
    exact ⟨fill_mono h.1 sol_spec , (h.2.2.2.1 x sol_spec).symm⟩
  apply @reduce_to_new_axioms S' L₀' op
  . ext x
    apply (Filter.eventually_const (f := f)).mp
    filter_upwards [L₀'_lim x, L₀'_lim (L₀' x)] with sol h1 h2
    simp only [fill, Set.mem_setOf_eq] at h1
    obtain ⟨ y, ⟨ m, hx⟩, hy ⟩ := h1.1
    change L₀' (L₀' x) = x * (e 0)⁻¹
    have := sol.1.axiom_i'' y (sol.1.L₀' y) hy rfl m
    rw [←h2.2, ←h1.2, hx, this.2.1, this.2.2, mul_assoc]
    congr
    exact zpow_sub_one (e 0) m
  . intro a x y h
    apply (Filter.eventually_const (f := f)).mp
    filter_upwards [L₀'_lim ((R' (S (a - S' x))) y), L₀'_lim ((R' (S (S' y))) ((R' (a - S' x)).symm (L₀' ((R' (S (a - S' x))) y)))), S'_lim x, S'_lim y] with sol h1 h2 h3 h4
    rw [←h2.2, ←h1.2, ←h3.2, ←h4.2]
    exact (sol.1.axiom_iii'' x y a h3.1 h4.1 h).2.2
  . intro x
    apply (Filter.eventually_const (f := f)).mp
    filter_upwards [L₀'_lim ((R' (S (S' x))) x), L₀'_lim ((R' (S (S' x))) ((R' (S' x)).symm (L₀' ((R' (S (S' x))) x)))), S'_lim x] with sol h1 h2 h3
    rw [←h2.2, ←h1.2, ←h3.2]
    exact (sol.1.axiom_iv'' x h3.1).2.2
  . intro x
    apply (Filter.eventually_const (f := f)).mp
    filter_upwards [op_lim x x, S'_lim x] with sol h1 h2
    rw [←h2.2, ←h1.2]
    exact (sol.1.axiom_v'' x h1.1).2
  . intro y a
    apply (Filter.eventually_const (f := f)).mp
    filter_upwards [op_lim (R' a y) y, S'_lim y] with sol h1 h2
    rw [←h2.2, ←h1.2]
    exact (sol.1.axiom_vi'' y a h1.1).2
  -- this one is a little trickier than the previous axioms because it involves a variable z that is not initially defined
  intro x y h h'
  have : ∃ z, op x y = Sum.inr z := by
    apply (Filter.eventually_const (f := f)).mp
    filter_upwards [op_lim x y] with sol h1
    rw [←h1.2]
    obtain ⟨ z, this, _ ⟩ :=  sol.1.axiom_vii'' x y h h' h1.1
    exact ⟨ z, this ⟩
  obtain ⟨ z, hz ⟩ := this
  refine ⟨ z, hz, ?_ ⟩
  apply (Filter.eventually_const (f := f)).mp
  filter_upwards [op_lim z x, op_lim x y, L₀'_lim ((R' 0) ((R' (S' x)) y)), S'_lim x] with sol h1 h2 h3 h4
  rw [←h1.2, ←h3.2, ←h4.2]
  have := sol.1.axiom_vii'' x y h h' h2.1
  obtain ⟨ z', hz1, hz2, hz3, hz4, hz5 ⟩ := this
  rw [h2.2,hz] at hz1
  simp only [Sum.inr.injEq] at hz1
  rwa [←hz1] at hz5

-- `generators A` are all the indices in ℕ involved in a finite set `A` of elements of `SM`
abbrev generators (A : Finset SM) : Finset ℕ := Finset.biUnion A DFinsupp.support ∪ {0}

abbrev in_generators (A : Finset SM) (a : SM) := a.support ⊆ generators A

@[simp]
lemma support_E (d:ℕ) : (E d).support = {d} := by
  rw [DirectSum.support_of]
  exact Ne.symm (ne_of_beq_false rfl)

lemma E_in_generators {A : Finset SM} {d: ℕ} (h: d ∈ generators A) : in_generators A (E d) := by
  rwa [in_generators, support_E, Finset.singleton_subset_iff]

lemma not_in_generators {A : Finset SM} {a : SM} (h: in_generators A a) {n:ℕ} (hn: ¬ n ∈ generators A): a n = 0 := by
  contrapose! hn
  rw [← DFinsupp.mem_support_toFun] at hn
  exact Finset.mem_of_subset h hn

lemma zero_in_generators (A : Finset SM): 0 ∈ generators A := Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)

lemma generators_nonempty (A : Finset SM): (generators A).Nonempty := ⟨ 0, zero_in_generators A ⟩

lemma mem_in_generators {A : Finset SM} {a : SM} (h: a ∈ A) : in_generators A a := by
  exact (Finset.subset_biUnion_of_mem _ h).trans Finset.subset_union_left

lemma sum_in_generators {A : Finset SM} {a b : SM} (ha: in_generators A a) (hb: in_generators A b) : in_generators A (a+b) := by
  intro n hn
  simp only [DFinsupp.mem_support_toFun, DirectSum.add_apply, ne_eq] at hn
  contrapose! hn
  simp only [not_in_generators ha hn, not_in_generators hb hn, add_zero]

lemma S_in_generators {A : Finset SM} {a : SM} (ha: in_generators A a) : in_generators A (S a) := sum_in_generators ha ha

lemma diff_in_generators {A : Finset SM} {a b : SM} (ha: in_generators A a) (hb: in_generators A b) : in_generators A (a-b) := by
  intro n hn
  simp only [DFinsupp.mem_support_toFun, DirectSum.sub_apply, ne_eq] at hn
  contrapose! hn
  simp only [not_in_generators ha hn, not_in_generators hb hn, sub_zero]

-- a fresh generator that does not appear in A
abbrev fresh (A: Finset SM) (n:ℕ) : ℕ := ((generators A).max' (generators_nonempty A)) + (n + 1)

lemma fresh_ne_fresh (A: Finset SM) (n m:ℕ) (h: n ≠ m) : fresh A n ≠ fresh A m := by
  contrapose! h
  rwa [add_right_inj, add_left_inj] at h

lemma fresh_ne_generator (A: Finset SM) (n:ℕ) : ¬ (fresh A n) ∈ generators A := by
  by_contra! h
  linarith [Finset.le_max' _ _ h]

lemma fresh_not_in_generators (A: Finset SM) (n:ℕ) : ¬ in_generators A (E (fresh A n)) := by
  simp only [in_generators, support_E, Finset.singleton_subset_iff]
  exact fresh_ne_generator A n

abbrev basis_elements (x:N) : Finset SM := Finset.image (fun (a, _) ↦ a) x.toWord.toFinset ∪ {0}

abbrev basis_elements' (x:M) : Finset SM := match x with
  | Sum.inl a => {a}
  | Sum.inr x => basis_elements x

@[simp]
lemma basis_elements_of_id : basis_elements 1 = {0} := by
  simp only [Finset.union_eq_right, FreeGroup.toWord_one, List.toFinset_nil, Finset.image_empty,
    Finset.subset_singleton_iff, true_or]

@[simp]
lemma basis_elements_of_generator (a: SM) : basis_elements (e a) = {a,0} := by
  simp only [basis_elements, FreeGroup.toWord_of, List.toFinset_cons, List.toFinset_nil,
    insert_emptyc_eq, Finset.image_singleton]
  rfl

lemma basis_elements_of_mul (x y:N): basis_elements (x * y) ⊆ basis_elements x ∪ basis_elements y := by
  unfold basis_elements
  simp only [Finset.union_assoc]
  rw [Finset.union_comm {0} _, Finset.union_assoc, Finset.union_idempotent, ← Finset.union_assoc, ← Finset.image_union]
  gcongr
  apply Finset.image_subset_image
  intro n hn
  simp at hn ⊢
  replace hn := List.Sublist.mem hn (FreeGroup.toWord_mul_sublist x y)
  rwa [List.mem_append] at hn

/-- For Mathlib? -/
@[simp]
lemma List.toFinset_map {α β: Type*} [DecidableEq α] [DecidableEq β] (l: List α) (f : α → β) : (List.map f l).toFinset = Finset.image f l.toFinset := by
  ext a
  simp_all only [List.mem_toFinset, List.mem_map, Finset.mem_image]


@[simp]
lemma basis_elements_of_inv (x:N) : basis_elements x⁻¹ = basis_elements x := by
  unfold basis_elements
  congr 1
  simp only [FreeGroup.toWord_inv, FreeGroup.invRev, List.toFinset_reverse, List.toFinset_map, Finset.image_image]
  congr

@[simp]
lemma basis_elements_of_genzero_pow' (n: ℕ) : basis_elements ((e 0)^n) = {0} := by
  unfold basis_elements
  classical
  simp
  rw [Decidable.or_iff_not_imp_left]
  intro hn
  ext m
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_replicate, ne_eq, hn, not_false_eq_true,
    true_and, eq_comm, exists_eq_left, Finset.mem_singleton]

@[simp]
lemma basis_elements_of_genzero_pow (n: ℤ) : basis_elements ((e 0)^n) = {0} := match n with
 | Int.ofNat m => by
    simp only [Int.ofNat_eq_coe, zpow_natCast, basis_elements_of_genzero_pow']
 | Int.negSucc m => by
    rw [Int.negSucc_coe, zpow_neg, basis_elements_of_inv, zpow_natCast, basis_elements_of_genzero_pow']

lemma basis_elements_of_rel' {x y:N} (h: x ≈ y) : basis_elements x ⊆ basis_elements y := by
  obtain ⟨ n, hn ⟩ := rel_def (Setoid.symm h)
  rw [hn]
  apply (basis_elements_of_mul _ _).trans
  rw [basis_elements_of_genzero_pow]
  simp only [Finset.union_assoc, Finset.union_idempotent, subset_refl]

lemma basis_elements_of_rel {x y:N} (h: x ≈ y) : basis_elements x = basis_elements y := by
  ext a
  constructor
  . intro h2
    exact basis_elements_of_rel' h h2
  intro h2
  exact basis_elements_of_rel' (Setoid.symm h) h2

/-- All the elements of `SM` that are involved in a partial solution, plus an additional set of extra elements of `N`-/
abbrev PartialSolution.involved_elements (sol: PartialSolution) (extras: Finset N) : Finset SM := Finset.biUnion sol.Predom_L₀' basis_elements ∪ Finset.biUnion sol.Dom_S' basis_elements ∪ Finset.image  sol.S' sol.Dom_S' ∪ Finset.biUnion sol.Dom_op (fun (x, _) ↦ basis_elements x) ∪ Finset.biUnion sol.Dom_op (fun (_, y) ↦ basis_elements y) ∪ Finset.biUnion sol.Dom_op (fun (x, y) ↦ basis_elements' (sol.op x y)) ∪ Finset.biUnion extras basis_elements

lemma PartialSolution.extras_involved (sol: PartialSolution) (extras: Finset N) {x : N} (hx: x ∈ extras) : basis_elements x ⊆ sol.involved_elements extras := calc
  _ ⊆ Finset.biUnion extras basis_elements := Finset.subset_biUnion_of_mem _ hx
  _ ⊆ _ := Finset.subset_union_right

lemma PartialSolution.dom_L₀'_involved (sol: PartialSolution) (extras: Finset N) {x : N} (hx: x ∈ fill sol.Predom_L₀') : basis_elements x ⊆ sol.involved_elements extras := calc
  _ ⊆ Finset.biUnion sol.Predom_L₀' basis_elements := by
    simp [fill] at hx
    obtain ⟨ y, hxy, hy ⟩ := hx
    rw [<-basis_elements_of_rel hxy]
    exact Finset.subset_biUnion_of_mem _ hy
  _ ⊆ _ := by
    intro _
    simp only [Finset.mem_union]
    tauto


/-- All the indices in ℕ that are involved in a partial solution, plus an additional set of extra elements of `N`-/
abbrev PartialSolution.involved_generators (sol : PartialSolution) (extras: Finset N): Finset ℕ := generators (sol.involved_elements extras)

abbrev PartialSolution.fresh_generator (sol : PartialSolution) (extras: Finset N) (n:ℕ) : ℕ := fresh (sol.involved_elements extras) n


open Classical in
/-- Extend a map L₀' to map (R' 0)^n x to (R' 0)^n y and (R' 0)^n y to (R' 0)^(n-1) x for all integers n.  One should also add x and y to the predomain when extending. -/
noncomputable abbrev extend (x y:N) (L₀': N → N) (z : N): N :=
  if z ≈ x then y * x⁻¹ * z else (if z ≈ y then x * (e 0)⁻¹ * y⁻¹ * z else L₀' z)

lemma extend_not_rel {x y:N} (L₀': N → N) {z : N} (hx: ¬ z ≈ x) (hy: ¬ z ≈ y) : extend x y L₀' z = L₀' z := by
  simp only [extend, hx, hy, if_false, if_false]

def enlarge_L₀'_extends' (L₀': N → N) {x y:N} {A: Finset N} (hx: x ∉ fill A) (hy: y ∉ fill A) {z:N} (hz: z ∈ fill A) : extend x y L₀' z = L₀' z := by
  apply extend_not_rel _
  . contrapose! hx
    exact (fill_invar _ hx).mp hz
  contrapose! hy
  exact (fill_invar _ hy).mp hz

def enlarge_L₀'_extends {sol : PartialSolution} {x y:N} (hx: x ∉ fill sol.Predom_L₀') (hy: y ∉ fill sol.Predom_L₀') {z:N} (hz: z ∈ fill sol.Predom_L₀') : extend x y sol.L₀' z = sol.L₀' z := enlarge_L₀'_extends' sol.L₀' hx hy hz

lemma extend_axiom_i'' {L₀' : N → N} {Predom: Finset N} (h: axiom_i'' L₀' Predom) {x y:N} (hx: x ∉ fill Predom) (hy: y ∉ fill Predom) (hneq : ¬ y ≈ x): axiom_i'' (extend x y L₀') (Predom ∪ {x,y}) := by
  intro z w hz hw n
  simp only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at hz
  rcases hz with hz | hz | hz
  . rw [← hw, hz]
    refine ⟨ ?_, ?_, ?_ ⟩
    . simp only [fill, Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, Set.mem_setOf_eq]
      use y
      simp only [extend, Setoid.refl x, ↓reduceIte, inv_mul_cancel_right, Setoid.refl y, or_true,
        and_self]
    . simp only [extend, Setoid.symm (rel_of_mul x n), ↓reduceIte, Setoid.refl x, inv_mul_cancel_right]
      group
    have : extend x y L₀' x = y := by
      simp only [extend, Setoid.refl x, ↓reduceIte, inv_mul_cancel_right]
    rw [this]
    have : ¬ y * e 0 ^ n ≈ x := by
      contrapose! hneq
      exact Setoid.trans (rel_of_mul y n) hneq
    simp [extend, hneq, Setoid.refl x, Setoid.refl y, Setoid.symm (rel_of_mul y n), this]
    group
  . rw [← hw]
    rw [enlarge_L₀'_extends' L₀' hx hy (subset_fill _ hz), enlarge_L₀'_extends' L₀' hx hy ((fill_invar _ (rel_of_mul (L₀' z) n)).mp (h z (L₀' z) hz rfl 0).1), enlarge_L₀'_extends' L₀' hx hy (fill_invar' _ (subset_fill _ hz) n)]
    refine ⟨ ?_, (h z (L₀' z) hz rfl n).2.1, (h z (L₀' z) hz rfl n).2.2 ⟩
    replace h := (h z (L₀' z) hz rfl 0).1
    simp only [fill, Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, Set.mem_setOf_eq] at h ⊢
    obtain ⟨ u, hu, hu' ⟩ := h
    refine ⟨ u, hu, Or.inr (Or.inl hu') ⟩

  have hyx : ¬ y * (e 0)^n ≈ x := by
    contrapose! hneq
    exact Setoid.trans (rel_of_mul y n) hneq
  rw [← hw, hz]
  refine ⟨ ?_, ?_, ?_ ⟩
  . simp only [fill, Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, Set.mem_setOf_eq]
    use x
    simp only [extend, hneq, ↓reduceIte, Setoid.refl y, inv_mul_cancel_right, rel_iff,
      mul_right_inj, true_or, and_true]
    use -1
    rfl
  . simp only [extend, hyx, ↓reduceIte, Setoid.symm (rel_of_mul y n), hneq, Setoid.refl y,
    inv_mul_cancel_right]
    group
  have : extend x y L₀' y = x * (e 0)⁻¹ := by
    simp only [extend, hneq, ↓reduceIte, Setoid.refl y, inv_mul_cancel_right]
  rw [this]
  have : x * (e 0)⁻¹ * e 0 ^ n = x * (e 0) ^ (n-1) := by group
  rw [this]
  simp [extend, Setoid.symm (rel_of_mul x (n-1))]
  group

lemma gen_fresh_not_in_fill (sol : PartialSolution) (extras: Finset N) (n:ℕ) : e (E (sol.fresh_generator extras n)) ∉ fill sol.Predom_L₀' := by
  by_contra hed
  replace hed := PartialSolution.dom_L₀'_involved sol extras hed
  simp only [basis_elements_of_generator] at hed
  replace hed := mem_in_generators (hed (Finset.mem_insert_self (E (sol.fresh_generator extras n)) {0}))
  exact fresh_not_in_generators (sol.involved_elements extras) n hed

lemma gen_fresh_not_rel_extra (sol : PartialSolution) {extras: Finset N} (n:ℕ) {x:N} (hx: x ∈ extras) : ¬ e (E (sol.fresh_generator extras n)) ≈ x := by
  set d:= E (sol.fresh_generator extras n)
  by_contra! h
  replace h := basis_elements_of_rel h
  simp only [basis_elements_of_generator] at h
  have : in_generators (sol.involved_elements extras) d := by
    apply mem_in_generators
    apply sol.extras_involved extras hx
    rw [← h]
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
  simp only [in_generators, d, support_E, Finset.singleton_subset_iff] at this
  exact fresh_ne_generator (sol.involved_elements extras ) n this

noncomputable def enlarge_L₀'_by {sol : PartialSolution} {x y:N} (hx: x ∉ fill sol.Predom_L₀') (hy: y ∉ fill sol.Predom_L₀') (hneq: ¬ y ≈ x): PartialSolution := {
    L₀' := extend x y sol.L₀'
    op := sol.op
    S' := sol.S'
    I := sol.I
    Predom_L₀' := sol.Predom_L₀' ∪ {x, y}
    Dom_op := sol.Dom_op
    Dom_S' := sol.Dom_S'
    axiom_i'' := extend_axiom_i'' sol.axiom_i'' hx hy hneq
    axiom_S := PartialSolution.axiom_S
    axiom_iii'' := by
      intro x' y' a hx' hy' h
      have := sol.axiom_iii'' x' y' a hx' hy' h
      rw [enlarge_L₀'_extends hx hy this.1, enlarge_L₀'_extends hx hy this.2.1]
      refine ⟨ (fill_mono Finset.subset_union_left) this.1, (fill_mono Finset.subset_union_left) this.2.1, this.2.2 ⟩

    axiom_iv'' := by
      intro x' hx'
      have := sol.axiom_iv'' x' hx'
      rw [enlarge_L₀'_extends hx hy this.1, enlarge_L₀'_extends hx hy this.2.1]
      refine ⟨ (fill_mono Finset.subset_union_left) this.1, (fill_mono Finset.subset_union_left) this.2.1, this.2.2 ⟩
    axiom_v'' := sol.axiom_v''
    axiom_vi'' := sol.axiom_vi''
    axiom_vii'' := by
      intro x' y' h1 h2 h3
      obtain ⟨ z, h3, h4, h5, h6, h7 ⟩ := sol.axiom_vii'' x' y' h1 h2 h3
      refine ⟨ z, h3, h4, h5, (fill_mono Finset.subset_union_left) h6, ?_ ⟩
      convert h7 using 3
      exact enlarge_L₀'_extends hx hy h6
    axiom_P := sol.axiom_P
}


lemma enlarge_L₀' (sol : PartialSolution) (x:N)  : ∃ sol' : PartialSolution, sol ≤ sol' ∧ x ∈ fill sol'.Predom_L₀' := by
  by_cases hx : x ∈ fill sol.Predom_L₀'
  . exact ⟨ sol, PartialSolution_refl sol, hx ⟩
  have hed : (e $ E $ sol.fresh_generator {x} 0) ∉ fill sol.Predom_L₀' := gen_fresh_not_in_fill sol {x} 0

  set sol' : PartialSolution := enlarge_L₀'_by hx hed (gen_fresh_not_rel_extra sol 0 (Finset.mem_singleton.mpr rfl))

  refine ⟨ sol', ?_, ?_ ⟩
  . refine ⟨ Finset.subset_union_left, by rfl, by rfl, ?_, ?_, ?_ ⟩
    . intro x' hx'
      exact (enlarge_L₀'_extends hx hed hx').symm
    . intros; rfl
    intros; rfl
  apply subset_fill
  rw [Finset.mem_coe]
  apply Finset.mem_union_right
  simp only [Finset.mem_insert, Finset.mem_singleton, true_or]

lemma enlarge_S' (sol : PartialSolution) (x:N) : ∃ sol' : PartialSolution, sol ≤ sol' ∧ x ∈ sol'.Dom_S' := by sorry

lemma enlarge_op (sol : PartialSolution) (x y :N) : ∃ sol' : PartialSolution, sol ≤ sol' ∧ (x,y) ∈ sol'.Dom_op := by
  wlog hx : x ∈ sol.Dom_S'
  . obtain ⟨ sol', hsol, hx ⟩ := enlarge_S' sol x
    obtain ⟨ sol'', hsol', hx' ⟩ := this sol' x y hx
    exact ⟨ sol'', hsol.trans hsol', hx' ⟩
  wlog hy : y ∈ sol.Dom_S'
  . obtain ⟨ sol', hsol, hy ⟩ := enlarge_S' sol y
    obtain ⟨ sol'', hsol', hy' ⟩ := this sol' x y (hsol.2.2.1 hx) hy
    exact ⟨ sol'', hsol.trans hsol', hy' ⟩
  have no_pending : ¬ ∃ z, (y,z,x) ∈ sol.I := by
    by_contra this
    obtain ⟨ z, hz ⟩ := this
    have := sol.axiom_P y z x hz
    exact this.1 hy
  by_cases hdef : (x,y) ∈ sol.Dom_op
  . exact ⟨ sol, PartialSolution_refl sol, hdef ⟩
  by_cases hxy : x = y
  . rw [←hxy] at hdef no_pending ⊢
    set sol' : PartialSolution := {
      L₀' := sol.L₀'
      op := fun x' y' ↦ if (x',y') = (x,x) then Sum.inl (sol.S' x) else sol.op x' y'
      S' := sol.S'
      Predom_L₀' := sol.Predom_L₀'
      Dom_op := sol.Dom_op ∪ {(x,x)}
      Dom_S' := sol.Dom_S'
      I := sol.I
      axiom_i'' := sol.axiom_i''
      axiom_S := sol.axiom_S
      axiom_iii'' := sol.axiom_iii''
      axiom_iv'' := sol.axiom_iv''
      axiom_v'' := by
        intro x' hx'
        simp only [Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq, and_self] at hx'
        rcases hx' with hx' | hx'
        . have := sol.axiom_v'' x' hx'
          by_cases hxx' : x' = x
          . simp only [hxx', hx, ↓reduceIte, and_self]
          simp only [this, Prod.mk.injEq, hxx', and_self, ↓reduceIte]
        simp only [hx', hx, ↓reduceIte, and_self]
      axiom_vi'' := by
        intro y' a hya
        have : ¬ (R' a y' = x ∧ y' = x) := by
          by_contra this
          obtain ⟨ h1, h2 ⟩ := this
          rw [<-h2] at h1
          simp only [R', Equiv.coe_fn_mk, mul_right_eq_self, FreeGroup.of_ne_one] at h1
        simp [this]
        have hya' : (R' a y', y') ∈ sol.Dom_op := by
          simp only [Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq] at hya
          tauto
        exact sol.axiom_vi'' y' a hya'
      axiom_vii'' := by
        intro x' y' hxy' hxay hop
        have hop' : (x',y') ∈ sol.Dom_op := by
          simp only [Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq] at hop
          rcases hop  with hop | hop
          . exact hop
          rw [hop.2] at hxy'
          exfalso
          exact hxy' hop.1
        have hne : (x',y') ≠ (x,x) := by
          contrapose! hxy'
          simp only [Prod.mk.injEq] at hxy'
          rw [hxy'.1, hxy'.2]

        obtain ⟨ z, h1, h2, h3, h4, h5 ⟩ := sol.axiom_vii'' x' y' hxy' hxay hop'
        have hzne : ¬ (z = x ∧ x' = x) := by
          by_contra hzne
          rw [hzne.1, hzne.2] at h2
          exact no_pending ⟨ y', h2 ⟩
        simp only [hne, ↓reduceIte, Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq]
        refine ⟨z, h1, h2, Or.inl h3, h4, ?_ ⟩
        rw [if_neg hzne]
        exact h5
      axiom_P := by
        intro x' y' z hI
        obtain ⟨ h1, h2, h3, h4 ⟩ := sol.axiom_P x' y' z hI
        refine ⟨ h1, ?_, h3, h4 ⟩
        simp only [Finset.mem_union, h2, Finset.mem_singleton, Prod.mk.injEq, false_or, not_and]
        intro hzx
        rw [hzx] at h3
        exact id (Ne.symm h3)
    }
    refine ⟨ sol', ?_, ?_ ⟩
    . refine ⟨ by rfl, ?_, by rfl, ?_, ?_, ?_ ⟩
      . exact Finset.union_subset_left fun ⦃a⦄ a ↦ a
      . intros; rfl
      . intro (x',y') hxy
        have : (x',y') ≠ (x,x) := by
          contrapose! hdef
          rwa [hdef] at hxy
        dsimp [sol']
        simp only [this, ↓reduceIte]
      intros; rfl
    apply Finset.mem_union_right
    exact Finset.mem_singleton.mpr rfl
  by_cases hray : ∃ a, x = R' a y
  . obtain ⟨ a, hray ⟩ := hray
    rw [hray] at hx no_pending hdef hxy ⊢
    set sol' : PartialSolution := {
      L₀' := sol.L₀'
      op := fun x' y' ↦ if (x',y') = ((R' a) y,y) then Sum.inl (a - sol.S' y) else sol.op x' y'
      S' := sol.S'
      Predom_L₀' := sol.Predom_L₀'
      Dom_op := sol.Dom_op ∪ {((R' a) y,y)}
      Dom_S' := sol.Dom_S'
      I := sol.I
      axiom_i'' := sol.axiom_i''
      axiom_S := sol.axiom_S
      axiom_iii'' := sol.axiom_iii''
      axiom_iv'' := sol.axiom_iv''
      axiom_v'' := by
        intro x' hx'
        have : (x',x') ≠ ((R' a) y, y) := by
          contrapose! hxy
          simp only [Prod.mk.injEq] at hxy
          rw [<-hxy.1, ←hxy.2]
        simp only [Finset.mem_union, Finset.mem_singleton, this, or_false] at hx'
        simp only [this, ↓reduceIte]
        exact sol.axiom_v'' x' hx'
      axiom_vi'' := by
        intro y' a' hy'
        simp only [Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq] at hy'
        by_cases heq : (R' a') y' = (R' a) y ∧ y' = y
        . rw [heq.1, heq.2]
          simp only [hy, ↓reduceIte, Sum.inl.injEq, sub_left_inj, true_and]
          have := heq.1
          rw [heq.2] at this
          simp [R', e, FreeGroup.of_injective.eq_iff] at this
          exact this.symm
        have :  ((R' a') y', y') ∈ PartialSolution.Dom_op := by tauto
        simp only [Prod.mk.injEq, heq, ↓reduceIte]
        exact sol.axiom_vi'' y' a' this
      axiom_vii'' := by
        intro x' y' hxy' hneq hin
        have h1 : (x',y') ≠ (R' a y, y) := by
          contrapose! hxy'
          simp only [Prod.mk.injEq] at hxy'
          have := hxy'.1
          rw [← hxy'.2] at this
          exfalso
          exact hneq a this

        have h2 : (x',y') ∈ sol.Dom_op := by
          by_contra hin'
          simp only [Finset.mem_union, hin', Finset.mem_singleton, Prod.mk.injEq, false_or, h1] at hin
        simp only [h1, ↓reduceIte, Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq]
        obtain ⟨ z, h3, h4, h5, h6, h7 ⟩ := sol.axiom_vii'' x' y' hxy' hneq h2
        refine ⟨ z, h3, h4, Or.inl h5, h6, ?_ ⟩
        have h8 : ¬ (z = (R' a) y ∧ x' = y) := by
          contrapose! hdef
          rwa [hdef.1, hdef.2] at h5
        rwa [if_neg h8]
      axiom_P := by
        intro x' y' z' hI
        obtain ⟨ h1, h2, h3 ⟩ := sol.axiom_P x' y' z' hI
        refine ⟨ h1, ?_, h3 ⟩
        simp only [Finset.mem_union, h2, Finset.mem_singleton, Prod.mk.injEq, false_or]
        by_contra h4
        obtain ⟨ h4, h5 ⟩ := h4
        rw [←h5] at h4
        exact h3.2 a h4
    }
    refine ⟨ sol', ?_, ?_ ⟩
    . refine ⟨ by rfl, ?_, by rfl, ?_, ?_, ?_ ⟩
      . exact Finset.union_subset_left fun ⦃a⦄ a ↦ a
      . intros; rfl
      . intro (x',y') hxy
        have : (x',y') ≠ (R' a y,y) := by
          contrapose! hdef
          rwa [hdef] at hxy
        dsimp [sol']
        simp only [this, ↓reduceIte]
      intros; rfl
    exact Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)
  set w := R' 0 $ R' (sol.S' x) $ y
  set d0 := E $ sol.fresh_generator {x,y,w} 0
  set d1 := E $ sol.fresh_generator {x,y,w} 1
  classical
  set new_L₀' := if w ∈ fill sol.Predom_L₀' then sol.L₀' else extend w (e d1) sol.L₀'
  set z' := (R' (S (sol.S' x))).symm $ new_L₀' w
  have hedw : ¬ e d1 ≈ w := by
    apply gen_fresh_not_rel_extra sol 1 _
    simp only [Finset.mem_insert, Finset.mem_singleton, or_true]
  have hed_notin : e d1 ∉ fill sol.Predom_L₀' := gen_fresh_not_in_fill sol {x, y, w} 1
  set sol' : PartialSolution := {
    L₀' := new_L₀'
    op := fun x' y' ↦ if (x',y') = (x,y) then Sum.inr $ e d0 else if (x',y') = (e d0,x) then Sum.inr z' else sol.op x y
    S' := sol.S'
    Predom_L₀' := if w ∈ fill sol.Predom_L₀' then sol.Predom_L₀' else sol.Predom_L₀' ∪ {w, e d1}
    Dom_op := sol.Dom_op ∪ { (x,y), (e d0, x) }
    Dom_S' := sol.Dom_S'
    I := sol.I ∪ {(e d0,x,z')}
    axiom_i'' := by
      by_cases hw : w ∈ fill sol.Predom_L₀'
      . simp only [hw, ↓reduceIte, new_L₀']
        exact sol.axiom_i''
      simp [hw, new_L₀']
      convert extend_axiom_i'' sol.axiom_i'' hw hed_notin hedw using 1
      simp_all only [not_exists, Finset.union_insert, d1, w]
    axiom_S := sol.axiom_S
    axiom_iii'' := by
      intro x' y' a hx' hy' hneq
      by_cases hw : w ∈ fill sol.Predom_L₀'
      . simp only [hw, ↓reduceIte, new_L₀']
        exact sol.axiom_iii'' x' y' a hx' hy' hneq
      simp only [hw, ↓reduceIte, new_L₀']
      obtain ⟨ h1, h2, h3 ⟩ := sol.axiom_iii'' x' y' a hx' hy' hneq
      have := enlarge_L₀'_extends hw hed_notin h1
      refine ⟨ fill_mono Finset.subset_union_left h1, ?_, ?_ ⟩
      . apply fill_mono Finset.subset_union_left _
        convert h2 using 3
      rw [this]
      convert h3 using 2
      apply enlarge_L₀'_extends hw hed_notin h2
    axiom_iv'' := by sorry
    axiom_v'' := by sorry
    axiom_vi'' := by sorry
    axiom_vii'' := by sorry
    axiom_P := by sorry
  }
  sorry


end Eq1729
