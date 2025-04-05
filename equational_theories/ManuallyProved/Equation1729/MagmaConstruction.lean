import Mathlib.Order.WithBot

import equational_theories.FreshGenerator
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.ManuallyProved.Equation1729.SmallMagma
import equational_theories.ManuallyProved.Equation1729.Edit

namespace Eq1729


abbrev axiom_i'' (L₀' : N → N) (Predom : Finset N) := ∀ (x y : N) (_: x ∈ Predom) (_ : L₀' x = y) (n:ℤ), y ∈ fill Predom ∧ L₀' ((e 0)^n * x) = (e 0)^n * y ∧ L₀' ((e 0)^n * y) = (e 0)^(n-1) * x

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
  axiom_vii'' (x y : N) (h : x ≠ y) (h' : ∀ a : SM, x ≠ R' a y) (hop: (x,y) ∈ Dom_op) : ∃ z : N, op x y = Sum.inr z ∧ ((x,y,z) ∈ I ∨ ((z,x) ∈ Dom_op ∧ x ∈ Dom_S' ∧ (R' 0 $ R' (S' x) $ y) ∈ fill Predom_L₀' ∧ op z x = Sum.inr ((R' (S (S' x))).symm $ L₀' $ R' 0 $ R' (S' x) $ y)))
  axiom_P (x y z : N) (h: (x,y,z) ∈ I) : x ∉ Dom_S' ∧ (z,x) ∉ Dom_op ∧ z ≠ x ∧ (∀ a : SM, z ≠ R' a x) ∧ (y ≠ x) ∧ (y ≠ parent x)
  axiom_P' (x y y' z : N) (hy : (x,y,z) ∈ I) (hy' : (x,y',z) ∈ I) : y = y'
  axiom_L (x:N) (a:SM) (h: x ∈ fill Predom_L₀') : L₀' x ≠ (R' a $ (R' (S a)).symm $ x)

abbrev PartialSolution.Dom_L₀' (sol: PartialSolution) : Set N := fill sol.Predom_L₀'

instance PartialSolution_LE : LE PartialSolution  := {
  le := by
    intro sol1 sol2
    exact sol1.Predom_L₀' ⊆ sol2.Predom_L₀' ∧ sol1.Dom_op ⊆ sol2.Dom_op ∧ sol1.Dom_S' ⊆ sol2.Dom_S' ∧ (∀ x, x ∈ fill sol1.Predom_L₀' → sol1.L₀' x = sol2.L₀' x) ∧ (∀ z ∈ sol1.Dom_op, sol1.op z.1 z.2 = sol2.op z.1 z.2) ∧ (∀ x ∈ sol1.Dom_S', sol1.S' x = sol2.S' x)
}

lemma PartialSolution.refl (sol : PartialSolution) : sol ≤ sol := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try {exact fun _ a ↦ a} <;> try {exact fun _ _ ↦ rfl}

/-- Impose a preorder on solutions using the notion of an extension. -/
instance PartialSolution_order : Preorder PartialSolution  := {
  le := PartialSolution_LE.le
  le_refl := PartialSolution.refl
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
  axiom_P' := by
    intro _ _ _ _ h
    contrapose! h
    exact Finset.not_mem_empty _
  axiom_L := by
    intro _ _ h
    contrapose! h
    simp only [fill_empty, Set.mem_empty_iff_false, not_false_eq_true]
}

lemma PartialSolution.R0_mem_L₀' {sol : PartialSolution} {x:N} (h:  x ∈ sol.Dom_L₀') : sol.L₀' x ∈ sol.Dom_L₀' := by
  simp [PartialSolution.Dom_L₀', fill] at h
  obtain ⟨ y, ⟨ n, _, _ ⟩, hy ⟩ := h
  have := sol.axiom_i'' y (L₀' y) hy (by rfl) n
  simp only [Dom_L₀', this.2.1, fill_invar', this.1]

lemma PartialSolution.inv_L₀' {sol : PartialSolution} {x:N} (h: x ∈ sol.Dom_L₀') : (sol.L₀' $ R' 0 $ sol.L₀' x) = x := by
  simp [PartialSolution.Dom_L₀', fill] at h
  obtain ⟨ y, ⟨ n, _, _ ⟩, hy ⟩ := h
  simp only [R', (sol.axiom_i'' y (L₀' y) hy (by rfl) n).2.1, Equiv.coe_fn_mk, <-mul_assoc]
  convert (sol.axiom_i'' y (L₀' y) hy (by rfl) (n+1)).2.2
  . group
  exact Eq.symm (Int.add_sub_cancel n 1)

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

lemma use_chain {sols : Set PartialSolution} (hchain: IsChain (fun (sol1 sol2 : PartialSolution) => sol1 ≤ sol2) sols ) (hnon: Nonempty sols) (htotal_L₀' : ∀ x : N, ∃ sol ∈ sols, x ∈ sol.Dom_L₀') (htotal_S' : ∀ x : N, ∃ sol ∈ sols, x ∈ sol.Dom_S') (htotal_op : ∀ (x y : N), ∃ sol ∈ sols, (x,y) ∈ sol.Dom_op) : ∃ (G: Type) (_: Magma G), Equation1729 G ∧ ¬ Equation817 G := by
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
    change L₀' (L₀' x) = (e 0)⁻¹ * x
    have := sol.1.axiom_i'' y (sol.1.L₀' y) hy rfl m
    rw [←h2.2, ←h1.2, hx, this.2.1, this.2.2, <-mul_assoc]
    congr
    group
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
  obtain ⟨ z', hz1, hz2 ⟩ := this
  rcases hz2 with hz2 | ⟨ hz3, hz4, hz5, hz6 ⟩
  . have := (sol.1.axiom_P x y z' hz2).2.1
    rw [h2.2, hz, Sum.inr.injEq] at hz1
    rw [←hz1] at this
    contrapose! this
    exact h1.1
  rw [h2.2,hz] at hz1
  simp only [Sum.inr.injEq] at hz1
  rwa [←hz1] at hz6


/-- All the elements of `SM` that are involved in a partial solution, plus an additional set of extra elements of `N`-/
abbrev PartialSolution.involved_elements (sol: PartialSolution) (extras: Finset N) : Finset SM := Finset.biUnion sol.Predom_L₀' basis_elements ∪ Finset.biUnion sol.Dom_S' basis_elements ∪ Finset.image  sol.S' sol.Dom_S' ∪ Finset.biUnion sol.Dom_op (fun (x, _) ↦ basis_elements x) ∪ Finset.biUnion sol.Dom_op (fun (_, y) ↦ basis_elements y) ∪ Finset.biUnion sol.Dom_op (fun (x, y) ↦ basis_elements' (sol.op x y)) ∪ Finset.biUnion sol.I (fun (x, _, _) ↦ basis_elements x) ∪ Finset.biUnion sol.I (fun (_, y, _) ↦ basis_elements y) ∪ Finset.biUnion sol.I (fun (_, _, z) ↦ basis_elements z) ∪ Finset.biUnion extras basis_elements

abbrev PartialSolution.directly_sees (sol:PartialSolution) (extras: Finset N) (x:N) := basis_elements x ⊆ sol.involved_elements extras

abbrev PartialSolution.directly_sees' (sol:PartialSolution) (extras: Finset N) (x:M) := basis_elements' x ⊆ sol.involved_elements extras

abbrev PartialSolution.sees (sol:PartialSolution) (extras: Finset N) (x:N) := generators (basis_elements x) ⊆ generators (sol.involved_elements extras)

abbrev PartialSolution.sees' (sol:PartialSolution) (extras: Finset N) (x:M) := generators (basis_elements' x) ⊆ generators (sol.involved_elements extras)

def PartialSolution.see_direct (sol:PartialSolution) {extras: Finset N} {x:N} (h: sol.directly_sees extras x) : sol.sees extras x := generators_mono h

def PartialSolution.see_direct' (sol:PartialSolution) {extras: Finset N} {x:M} (h: sol.directly_sees' extras x) : sol.sees' extras x := generators_mono h

abbrev PartialSolution.reaches (sol: PartialSolution) (extras: Finset N) (a:SM) := in_generators (sol.involved_elements extras) a

lemma PartialSolution.reaches_S (sol: PartialSolution) {extras: Finset N} {a:SM} (h: sol.reaches extras a) : sol.reaches extras (S a) := S_in_generators h

lemma PartialSolution.reaches_involved (sol: PartialSolution) {extras: Finset N} {a:SM} (h: a ∈ sol.involved_elements extras) : sol.reaches extras a := mem_in_generators h

lemma PartialSolution.sees_R'_inv (sol:PartialSolution) {extras: Finset N} {a:SM} {x:N} (ha: sol.reaches extras a) (hx: sol.sees extras x) : sol.sees extras $ (R' a).symm x := by
  dsimp [R', PartialSolution.sees]
  apply (generators_mono (basis_elements_of_mul _ _)).trans
  simp only [basis_elements_of_inv, basis_elements_of_generator]
  rw [generators_union]
  apply Finset.union_subset _ hx
  rw [generators_subset_iff]
  intro b hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with hb | hb
  . rw [hb]
    exact ha
  rw [hb]
  exact zero_in_generators' (sol.involved_elements extras)

lemma PartialSolution.extras_involved (sol: PartialSolution) (extras: Finset N) {x : N} (hx: x ∈ extras) : sol.sees extras x := by
  apply sol.see_direct
  calc
    _ ⊆ Finset.biUnion extras basis_elements := Finset.subset_biUnion_of_mem _ hx
    _ ⊆ _ := Finset.subset_union_right

lemma PartialSolution.dom_L₀'_involved' (sol: PartialSolution) (extras: Finset N) {x : N} (hx: x ∈ sol.Dom_L₀') : sol.sees extras x := by
  apply sol.see_direct
  exact calc
    _ ⊆ Finset.biUnion sol.Predom_L₀' basis_elements := by
      simp [PartialSolution.Dom_L₀', fill] at hx
      obtain ⟨ y, hxy, hy ⟩ := hx
      rw [←basis_elements_of_rel hxy]
      exact Finset.subset_biUnion_of_mem _ hy
    _ ⊆ _ := by
      intro _
      simp only [Finset.mem_union]
      tauto

lemma PartialSolution.dom_L₀'_involved (sol: PartialSolution) (extras: Finset N) {x : N} (hx: x ∈ sol.Dom_L₀') : sol.sees extras x ∧ sol.sees extras (sol.L₀' x) := by
  refine ⟨ sol.dom_L₀'_involved' extras hx, sol.dom_L₀'_involved' extras ?_ ⟩
  simp only [PartialSolution.Dom_L₀', fill, Set.mem_setOf_eq] at hx
  obtain ⟨ y, hxy, hy ⟩ := hx
  obtain ⟨ n, hn ⟩ := hxy
  have := sol.axiom_i'' y (sol.L₀' y) hy rfl n
  rw [hn, this.2.1]
  exact (fill_invar' _ _ n).mpr this.1

lemma PartialSolution.dom_S'_involved (sol: PartialSolution) (extras: Finset N) {x : N} (hx: x ∈ sol.Dom_S') : sol.sees extras x ∧ sol.S' x ∈ sol.involved_elements extras := by
    constructor
    . apply sol.see_direct
      intro a ha
      apply Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_right _ _
      simp only [Finset.mem_biUnion]
      exact ⟨ x, hx, ha ⟩
    apply Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_right _ _
    exact Finset.mem_image_of_mem S' hx

lemma PartialSolution.dom_op_involved (sol: PartialSolution) (extras: Finset N) {x y : N} (hxy: (x,y) ∈ sol.Dom_op) : sol.sees extras x ∧ sol.sees extras y ∧ sol.sees' extras (sol.op x y) := by
    refine ⟨ ?_, ?_, ?_ ⟩
    . apply see_direct
      intro a ha
      apply Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_right _ _
      simp only [Finset.mem_biUnion]
      exact ⟨ (x,y), hxy, ha ⟩
    . apply see_direct
      intro a ha
      apply Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_right _ _
      simp only [Finset.mem_biUnion]
      exact ⟨ (x,y), hxy, ha ⟩
    apply see_direct'
    intro a ha
    apply Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_right _ _
    simp only [Finset.mem_biUnion]
    exact ⟨ (x,y), hxy, ha ⟩

lemma PartialSolution.I_involved (sol: PartialSolution) (extras: Finset N) {x y z: N} (hxyz: (x,y,z) ∈ sol.I) : sol.sees extras x ∧ sol.sees extras y ∧ sol.sees extras z := by
    refine ⟨ ?_, ?_, ?_ ⟩
    . apply see_direct
      intro a ha
      apply Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_right _ _
      simp only [Finset.mem_biUnion]
      exact ⟨ (x,y,z), hxyz, ha ⟩
    . apply see_direct
      intro a ha
      apply Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_right _ _
      simp only [Finset.mem_biUnion]
      exact ⟨ (x,y,z), hxyz, ha ⟩
    apply see_direct
    intro a ha
    apply Finset.mem_union_left _ $ Finset.mem_union_right _ _
    simp only [Finset.mem_biUnion]
    exact ⟨ (x,y,z), hxyz, ha ⟩

/-- All the indices in ℕ that are involved in a partial solution, plus an additional set of extra elements of `N`-/
abbrev PartialSolution.involved_generators (sol : PartialSolution) (extras: Finset N): Finset ℕ := generators (sol.involved_elements extras)

abbrev PartialSolution.fresh_generator (sol : PartialSolution) (extras: Finset N) (n:ℕ) : ℕ := fresh (sol.involved_elements extras) n

lemma PartialSolution.fresh_not_involved (sol : PartialSolution) (extras : Finset N) (n:ℕ) : E (sol.fresh_generator extras n) ∉ sol.involved_elements extras := by
  have := fresh_not_in_generators (sol.involved_elements extras) n
  contrapose! this
  exact mem_in_generators this

lemma PartialSolution.fresh_not_in_gen (sol : PartialSolution) (extras : Finset N) (n:ℕ) : ¬ in_generators (sol.involved_elements extras) (E (sol.fresh_generator extras n)) := fresh_not_in_generators _ n


lemma PartialSolution.fresh_invis (sol : PartialSolution) (extras: Finset N) (n:ℕ) : ¬ sol.sees extras (e (E (sol.fresh_generator extras n))) := by
    by_contra h
    simp only [sees, basis_elements_of_generator, generators_subset_iff,
      Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, zero_in_generators', and_true, E_in_generators_iff] at h
    exact fresh_ne_generator (sol.involved_elements extras) n h

lemma PartialSolution.fresh_invis_pow (sol : PartialSolution) (extras: Finset N) (n:ℕ) {m:ℕ} (hm: m ≠ 0): ¬ sol.sees extras ((e (E (sol.fresh_generator extras n)))^m) := by
    by_contra h
    simp only [sees, basis_elements_of_generator_pow _ hm, generators_subset_iff,
      Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, zero_in_generators', and_true, E_in_generators_iff] at h
    exact fresh_ne_generator (sol.involved_elements extras) n h

open Classical in
/-- Extend a map L₀' to map (R' 0)^n x to (R' 0)^n y and (R' 0)^n y to (R' 0)^(n-1) x for all integers n.  One should also add x and y to the predomain when extending. -/
noncomputable abbrev PartialSolution.extend {sol:PartialSolution} (x y:N) (z : N): N :=
  if z ≈ x then z * x⁻¹ * y else (if z ≈ y then z * y⁻¹ * (e 0)⁻¹ * x else sol.L₀' z)

lemma PartialSolution.extend_not_rel {sol:PartialSolution} {x y:N} {z : N} (hx: ¬ z ≈ x) (hy: ¬ z ≈ y) : sol.extend x y z = sol.L₀' z := by
  simp only [extend, hx, hy, if_false, if_false]

def PartialSolution.enlarge_L₀'_extends' {sol:PartialSolution} {x y:N} (hx: x ∉ sol.Dom_L₀') (hy: y ∉ sol.Dom_L₀') {z:N} (hz: z ∈ sol.Dom_L₀') : sol.extend x y z = sol.L₀' z := by
  apply sol.extend_not_rel _
  . contrapose! hy
    exact (fill_invar _ hy).mp hz
  contrapose! hx
  exact (fill_invar _ hx).mp hz

lemma PartialSolution.enlarge_L₀'_extends {sol : PartialSolution} {x y:N} (hx: x ∉ sol.Dom_L₀') (hy: y ∉ sol.Dom_L₀') {z:N} (hz: z ∈ sol.Dom_L₀') : sol.extend x y z = sol.L₀' z := sol.enlarge_L₀'_extends' hx hy hz

lemma PartialSolution.enlarge_L₀'_new {sol : PartialSolution} {x y:N} (hneq: ¬ y ≈ x) (n: ℤ) : sol.extend x y (e 0 ^ n * x) = e 0 ^ n * y ∧ sol.extend x y (e 0 ^ n * y) = e 0 ^ (n-1) * x := by
  unfold PartialSolution.extend
  have h1 : (e 0)^n * x ≈ x := Setoid.symm $ rel_of_mul _ _
  have h2 : (e 0)^n * y ≈ y := Setoid.symm $ rel_of_mul _ _
  have h3 : ¬ (e 0)^n * y ≈ x := by contrapose! hneq; exact Setoid.trans (Setoid.symm h2) hneq
  simp only [h1, ↓reduceIte, mul_inv_cancel_right, h3, h2, mul_left_inj, true_and]
  group

lemma PartialSolution.enlarge_L₀'_new' {sol : PartialSolution} {x y:N} (hneq: ¬ y ≈ x) : sol.extend x y x= y ∧
sol.extend x y y = (e 0)⁻¹ * x := by
  convert sol.enlarge_L₀'_new hneq 0
  all_goals group

lemma PartialSolution.extend_axiom_i'' {sol : PartialSolution} {x y:N} (hx: x ∉ sol.Dom_L₀') (hy: y ∉ sol.Dom_L₀') (hneq : ¬ y ≈ x): Eq1729.axiom_i'' (sol.extend x y) (sol.Predom_L₀' ∪ {x,y}) := by
  intro z w hz hw n
  simp only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at hz
  rcases hz with rfl | hz | rfl
  . rw [(sol.enlarge_L₀'_new' hneq).1] at hw
    rw [← hw]
    refine ⟨ ?_, sol.enlarge_L₀'_new hneq n ⟩
    simp only [fill, Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, Set.mem_setOf_eq]
    use y
    simp only [or_true, and_true, Setoid.refl]
  . rw [← hw]
    rw [sol.enlarge_L₀'_extends' hx hy (subset_fill _ hz), sol.enlarge_L₀'_extends' hx hy ((fill_invar _ (rel_of_mul (L₀' z) n)).mp (axiom_i'' z (L₀' z) hz rfl 0).1), sol.enlarge_L₀'_extends' hx hy ((fill_invar' _ _ n).mpr (subset_fill _ hz))]
    refine ⟨ ?_, (axiom_i'' z (L₀' z) hz rfl n).2.1, (axiom_i'' z (L₀' z) hz rfl n).2.2 ⟩
    have h := (axiom_i'' z (L₀' z) hz rfl 0).1
    simp only [fill, Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, Set.mem_setOf_eq] at h ⊢
    obtain ⟨ u, hu, hu' ⟩ := h
    refine ⟨ u, hu, Or.inr (Or.inl hu') ⟩

  have hyx : ¬ (e 0)^n * z ≈ x := by
    contrapose! hneq
    exact Setoid.trans (rel_of_mul z n) hneq
  rw [(sol.enlarge_L₀'_new' hneq).2] at hw
  rw [← hw]
  refine ⟨ ?_, ?_, ?_ ⟩
  . simp only [fill_union, Set.mem_union, fill_pair, fill_singleton]
    right; left
    use 1; group
  . rw [(sol.enlarge_L₀'_new hneq n).2]
    group
  group
  exact (sol.enlarge_L₀'_new hneq _).1


lemma gen_fresh_not_in_fill (sol : PartialSolution) (extras: Finset N) (n:ℕ) : e (E (sol.fresh_generator extras n)) ∉ sol.Dom_L₀' := by
  have := fresh_not_in_generators (sol.involved_elements extras) n
  contrapose! this
  have h := (sol.dom_L₀'_involved extras this).1
  simp only [PartialSolution.sees, generators_subset_iff] at h
  apply h _ _
  simp only [basis_elements_of_generator, Finset.mem_singleton, Finset.mem_insert_self]

lemma gen_fresh_not_in_dom_S' (sol : PartialSolution) (extras: Finset N) (n:ℕ) : e (E (sol.fresh_generator extras n)) ∉ sol.Dom_S' := by
  have := fresh_not_in_generators (sol.involved_elements extras) n
  contrapose! this
  have h := (sol.dom_S'_involved extras this).1
  simp only [PartialSolution.sees, generators_subset_iff] at h
  apply h _ _
  simp only [basis_elements_of_generator, Finset.mem_insert_self]

lemma gen_fresh_pow_not_in_dom_S' (sol : PartialSolution) (extras: Finset N) (n:ℕ) {m:ℕ} (hm: m ≠ 0): (e (E (sol.fresh_generator extras n)))^m ∉ sol.Dom_S' := by
  have := fresh_not_in_generators (sol.involved_elements extras) n
  contrapose! this
  have h := (sol.dom_S'_involved extras this).1
  simp only [PartialSolution.sees, generators_subset_iff] at h
  apply h _ _
  simp only [basis_elements_of_generator_pow _ hm, Finset.mem_insert_self]

lemma gen_fresh_not_rel_extra (sol : PartialSolution) {extras: Finset N} (n:ℕ) {x:N} (hx: x ∈ extras) : ¬ e (E (sol.fresh_generator extras n)) ≈ x := by
  set d:= E (sol.fresh_generator extras n)
  by_contra! h
  replace h := basis_elements_of_rel h
  simp only [basis_elements_of_generator] at h
  have : in_generators (sol.involved_elements extras) d := by
    have := sol.extras_involved extras hx
    simp only [PartialSolution.sees, generators_subset_iff] at this
    apply this _ _
    simp only [← h, Finset.mem_insert, Finset.mem_singleton, true_or]
  simp only [in_generators, d, support_E, Finset.singleton_subset_iff] at this
  exact fresh_ne_generator (sol.involved_elements extras ) n this

-- will need a hypothesis to verify axiom L
noncomputable def enlarge_L₀'_by {sol : PartialSolution} {x y:N} (hx: x ∉ sol.Dom_L₀') (hy: y ∉ sol.Dom_L₀') (hneq: ¬ y ≈ x): PartialSolution := {
    L₀' := sol.extend x y
    op := sol.op
    S' := sol.S'
    I := sol.I
    Predom_L₀' := sol.Predom_L₀' ∪ {x, y}
    Dom_op := sol.Dom_op
    Dom_S' := sol.Dom_S'
    axiom_i'' := sol.extend_axiom_i'' hx hy hneq
    axiom_S := sol.axiom_S
    axiom_iii'' := by
      intro x' y' a hx' hy' h
      have := sol.axiom_iii'' x' y' a hx' hy' h
      rw [sol.enlarge_L₀'_extends hx hy this.1, sol.enlarge_L₀'_extends hx hy this.2.1]
      refine ⟨ (fill_mono Finset.subset_union_left) this.1, (fill_mono Finset.subset_union_left) this.2.1, this.2.2 ⟩

    axiom_iv'' := by
      intro x' hx'
      have := sol.axiom_iv'' x' hx'
      rw [sol.enlarge_L₀'_extends hx hy this.1, sol.enlarge_L₀'_extends hx hy this.2.1]
      refine ⟨ (fill_mono Finset.subset_union_left) this.1, (fill_mono Finset.subset_union_left) this.2.1, this.2.2 ⟩
    axiom_v'' := sol.axiom_v''
    axiom_vi'' := sol.axiom_vi''
    axiom_vii'' := by
      intro x' y' h1 h2 h3
      obtain ⟨ z, h3, h4 ⟩ := sol.axiom_vii'' x' y' h1 h2 h3
      refine ⟨ z, h3, ?_ ⟩
      rcases h4 with h4 | ⟨ h5, h6, h7, h8 ⟩
      . exact Or.inl h4
      right
      refine ⟨ h5, h6, (fill_mono Finset.subset_union_left) h7, ?_ ⟩
      convert h8 using 3
      exact sol.enlarge_L₀'_extends hx hy h7
    axiom_P := sol.axiom_P
    axiom_P' := sol.axiom_P'
    axiom_L := by
      intro z a hz
      simp only [fill_union, fill_pair, fill_singleton, Set.mem_union] at hz
      rcases hz with hz | hz | hz
      . convert sol.axiom_L z a hz using 1
        apply sol.enlarge_L₀'_extends hx hy hz
      . obtain ⟨ n, rfl ⟩ := Setoid.symm hz
        sorry
      sorry
}


lemma enlarge_L₀' (sol : PartialSolution) (x:N)  : ∃ sol', sol ≤ sol' ∧ x ∈ fill sol'.Predom_L₀' := by
  by_cases hx : x ∈ sol.Dom_L₀'
  . exact ⟨ sol, sol.refl, hx ⟩
  have hed : (e $ E $ sol.fresh_generator {x} 0) ∉ sol.Dom_L₀' := gen_fresh_not_in_fill sol {x} 0

  set sol' : PartialSolution := enlarge_L₀'_by hx hed (gen_fresh_not_rel_extra sol 0 (Finset.mem_singleton.mpr rfl))

  refine ⟨ sol', ?_, ?_ ⟩
  . refine ⟨ Finset.subset_union_left, by rfl, by rfl, ?_, ?_, ?_ ⟩
    . intro x' hx'
      exact (sol.enlarge_L₀'_extends hx hed hx').symm
    . intros; rfl
    intros; rfl
  apply subset_fill
  rw [Finset.mem_coe]
  apply Finset.mem_union_right
  simp only [Finset.mem_insert, Finset.mem_singleton, true_or]

lemma PartialSolution.enlarge_L₀'_multiple (sol : PartialSolution) (A: Finset N)  : ∃ sol', sol ≤ sol' ∧ A.toSet ⊆ fill sol'.Predom_L₀' := by sorry

class PartialSolution_with_axioms extends PartialSolution where
  x : N
  hx : x ∉ Dom_S'
  hind : ∀ y:N, y < x → y ∈ Dom_S'
  hA : ∀ a, R' a x = parent x → R' (S' (parent x)) x ∈ fill Predom_L₀'
  hB : ∀ a, x = R' a (parent x) → R' (S (a - S' (parent x))) x ∈ fill Predom_L₀'
  hC : ∀ y z, (x,y,z) ∈ I → z ∈ Dom_S' → R' 0 (R' (S' z) x) ∈ fill Predom_L₀'

abbrev PartialSolution_with_axioms.y₀ (sol : PartialSolution_with_axioms) : N := parent sol.x

abbrev PartialSolution_with_axioms.extras (sol : PartialSolution_with_axioms) : Finset N := {sol.x, sol.y₀}

lemma PartialSolution_with_axioms.x_in_extras (sol : PartialSolution_with_axioms) : sol.x ∈ sol.extras := by
  simp only [PartialSolution_with_axioms.extras, Finset.mem_insert, Finset.mem_singleton, true_or]

lemma PartialSolution_with_axioms.y₀_in_extras (sol : PartialSolution_with_axioms) : sol.y₀ ∈ sol.extras := by
  simp only [PartialSolution_with_axioms.extras, Finset.mem_insert, Finset.mem_singleton, or_true]

/-- Data type to store the various L₀' extensions needed to prove `enlarge_S'_induction_with_axioms` -/
inductive L₀'_data (sol : PartialSolution_with_axioms) where
  | iv₁ : L₀'_data sol
  | iv₂ : L₀'_data sol
  | iii₁ (a:SM) (ha: R' a sol.x = sol.y₀) : L₀'_data sol
  | iii₂ (a:SM) (ha: sol.x = R' a sol.y₀) : L₀'_data sol
  | P (y z:N) (hI: (sol.x,y,z) ∈ sol.I) : L₀'_data sol

noncomputable instance  (sol : PartialSolution_with_axioms) : Fintype (L₀'_data sol) := by
  set embed : L₀'_data sol → Fin 4 ⊕ sol.I := fun data ↦ match data with
  | L₀'_data.iv₁ => Sum.inl 0
  | L₀'_data.iv₂ => Sum.inl 1
  | L₀'_data.iii₁ a ha => Sum.inl 2
  | L₀'_data.iii₂ a ha => Sum.inl 3
  | L₀'_data.P y z hI => Sum.inr ⟨ (sol.x,y,z), hI ⟩
  apply Fintype.ofInjective embed
  intro data data' h
  rcases data with ⟨⟩ | ⟨⟩ | ⟨a,ha⟩ | ⟨a,ha⟩ | ⟨y,z,hI⟩
  all_goals rcases data' with ⟨⟩ | ⟨⟩ | ⟨a',ha'⟩ | ⟨a',ha'⟩ | ⟨y',z',hI'⟩
  all_goals simp [embed] at h ⊢
  . exact R'_axiom_iia'.mp (ha' ▸ ha)
  . exact R'_axiom_iia'.mp (ha ▸ ha')
  exact h


/-- Data type to store the various op extensions needed to prove `enlarge_S'_induction_with_axioms` -/
inductive op_data (sol: PartialSolution_with_axioms) where
  | old (y z:N) (hop: (y,z) ∈ sol.Dom_op) : op_data sol
  | v : op_data sol
  | P₁ (y z:N) (hI: (sol.x,y,z) ∈ sol.I)  : op_data sol
  | P₂ (y z:N) (hI: (sol.x,y,z) ∈ sol.I) (hz : z ∈ sol.Dom_S') : op_data sol

noncomputable instance  (sol : PartialSolution_with_axioms) : Fintype (op_data sol) := by
  set embed : op_data sol → sol.Dom_op ⊕ Fin 1 ⊕ sol.I ⊕ sol.I := fun data ↦ match data with
  | op_data.old y z hop => Sum.inl ⟨ (y,z), hop ⟩
  | op_data.v => Sum.inr $ Sum.inl 0
  | op_data.P₁ y z hI => Sum.inr $ Sum.inr $ Sum.inl ⟨ (sol.x,y,z), hI ⟩
  | op_data.P₂ y z hI hz => Sum.inr $ Sum.inr $ Sum.inr ⟨ (sol.x,y,z), hI ⟩
  apply Fintype.ofInjective embed
  intro data data' h
  rcases data with ⟨y,z,hop⟩ | ⟨⟩ | ⟨y,z,hI⟩ | ⟨y,z,hI,hz⟩
  all_goals rcases data' with ⟨y',z',hop'⟩ | ⟨⟩ | ⟨y',z',hI'⟩ | ⟨y',z',hI',hz'⟩
  all_goals simp [embed] at h ⊢
  all_goals exact h


/-- Data type to store the various I extensions needed to prove `enlarge_S'_induction_with_axioms` -/
inductive I_data (sol: PartialSolution_with_axioms) where
  | old (x' y z:N) (hI: (x',y,z) ∈ sol.I) (hxx': sol.x ≠ x') : I_data sol
  | P₁ (y z:N) (hI: (sol.x,y,z) ∈ sol.I) (hz : z ∉ sol.Dom_S') : I_data sol
  | P₂ (y z:N) (hI: (sol.x,y,z) ∈ sol.I) (hz : z ∈ sol.Dom_S') : I_data sol

noncomputable instance  (sol : PartialSolution_with_axioms) : Fintype (I_data sol) := by
  set embed : I_data sol → sol.I ⊕ sol.I ⊕ sol.I := fun data ↦ match data with
  | I_data.old x' y z hI hxx' => Sum.inl ⟨ (x',y,z), hI ⟩
  | I_data.P₁ y z hI hz => Sum.inr $ Sum.inl ⟨ (sol.x,y,z), hI ⟩
  | I_data.P₂ y z hI hz => Sum.inr $ Sum.inr ⟨ (sol.x,y,z), hI ⟩
  apply Fintype.ofInjective embed
  intro data data' h
  rcases data with ⟨x',y,z,hI,hxx'⟩ | ⟨y,z,hI,hz⟩ | ⟨y,z,hI,hz⟩
  all_goals rcases data' with ⟨x'',y',z',hI',hxx''⟩ | ⟨y',z',hI',hz'⟩ | ⟨y',z',hI',hz'⟩
  all_goals { simp [embed] at h ⊢ ; try exact h }

noncomputable def  enum : N × N → ℕ := fun  p ↦ Exists.choose (Countable.exists_injective_nat (N × N)) p + 2

lemma enum_injective : Function.Injective enum := by
    intro _ _ h
    simp only [add_left_inj, enum] at h
    exact Exists.choose_spec (Countable.exists_injective_nat (N × N)) h

lemma enum_ne_0 (p : N × N) : enum p ≠ 0 := by dsimp [enum]; linarith

lemma enum_ne_1 (p : N × N) : enum p ≠ 1 := by dsimp [enum]; linarith

abbrev PartialSolution_with_axioms.d₀ (sol: PartialSolution_with_axioms) := E (sol.fresh_generator sol.extras 0)

abbrev PartialSolution_with_axioms.d₁ (sol: PartialSolution_with_axioms) := E (sol.fresh_generator sol.extras 1)

noncomputable abbrev PartialSolution_with_axioms.d (sol: PartialSolution_with_axioms) (y z: N) := E (sol.fresh_generator sol.extras (enum (y,z)))

lemma PartialSolution_with_axioms.d_injective (sol: PartialSolution_with_axioms) {y z y' z': N} (h: sol.d y z = sol.d y' z') : y = y' ∧ z = z' := by
  unfold PartialSolution_with_axioms.d E at h
  apply_fun (fun f ↦ f $ sol.fresh_generator sol.extras (enum (y,z))) at h
  have : sol.fresh_generator sol.extras (enum (y',z')) = sol.fresh_generator sol.extras (enum (y,z)) := by
    contrapose! h
    simp [DirectSum.of_eq_of_ne _ _ _ h]
    decide
  replace this := enum_injective $ fresh_injective _ this
  simp at this
  rw [this.1, this.2]
  tauto


lemma PartialSolution_with_axioms.noreach_invis (sol: PartialSolution_with_axioms) {a:SM} {y:N} (ha: ¬ sol.reaches sol.extras a) (hy: sol.sees sol.extras y): val a y = 0 := by
  apply val_of_nonsupp_eq_zero
  contrapose! ha
  exact ha.trans hy

lemma PartialSolution_with_axioms.sees_x (sol: PartialSolution_with_axioms) : sol.sees sol.extras x := sol.extras_involved _ sol.x_in_extras

lemma PartialSolution_with_axioms.sees_y₀ (sol: PartialSolution_with_axioms) : sol.sees sol.extras sol.y₀ := sol.extras_involved _ sol.y₀_in_extras

lemma PartialSolution_with_axioms.ad₀_noreach (sol: PartialSolution_with_axioms) {a:SM} (ha: R' a x = sol.y₀) : ¬ sol.reaches sol.extras (a - sol.d₀) := sorry

lemma PartialSolution_with_axioms.Sad₀_noreach (sol: PartialSolution_with_axioms) {a:SM} (ha: R' a x = sol.y₀) : ¬ sol.reaches sol.extras (S (a - sol.d₀)) := sorry

lemma PartialSolution_with_axioms.Sd₀_invis (sol: PartialSolution_with_axioms) {y:N} (hy: sol.sees sol.extras y): val (S sol.d₀) y = 0 := sol.noreach_invis (Sfresh_not_in_generators _ _) hy

lemma PartialSolution_with_axioms.d₀_invis (sol: PartialSolution_with_axioms) {y:N} (hy: sol.sees sol.extras y): val sol.d₀ y = 0 := sol.noreach_invis (fresh_not_in_generators _ _) hy

lemma PartialSolution_with_axioms.d₁_invis (sol: PartialSolution_with_axioms) {y:N} (hy: sol.sees sol.extras y): val sol.d₁ y = 0 := sol.noreach_invis (fresh_not_in_generators _ _) hy

lemma PartialSolution_with_axioms.d_invis (sol: PartialSolution_with_axioms) (y z:N) {w:N} (hw: sol.sees sol.extras w): val (sol.d y z) w = 0 := sol.noreach_invis (fresh_not_in_generators _ _) hw

lemma PartialSolution_with_axioms.ad₀_invis (sol: PartialSolution_with_axioms) {a:SM} {z:N} (ha: R' a x = sol.y₀) (hz: sol.sees sol.extras z): val (a - sol.d₀) z = 0 := sol.noreach_invis (sol.ad₀_noreach ha) hz

lemma PartialSolution_with_axioms.Sad₀_invis (sol: PartialSolution_with_axioms) {a:SM} {z:N} (ha: R' a x = sol.y₀) (hz: sol.sees sol.extras z): val (S (a - sol.d₀)) z = 0 := sol.noreach_invis (sol.Sad₀_noreach ha) hz


lemma PartialSolution_with_axioms.invis_lemma (sol: PartialSolution_with_axioms) (y z:N) : ¬ (sol.sees sol.extras $ (R' (S sol.d₀)).symm $ e $ sol.d y z) := by
    by_contra! this
    have hd₀ := sol.Sd₀_invis this
    have h : sol.d y z ≠ S sol.d₀ := E_ne_SE _ _
    simp only [R', Equiv.coe_fn_symm_mk, val_hom, val_inv, val_e, ↓reduceIte, Int.reduceNeg, h,
      add_zero, neg_eq_zero, one_ne_zero] at hd₀

lemma PartialSolution_with_axioms.invis_lemma' (sol: PartialSolution_with_axioms) (y z:N) (a:SM) : ¬ (sol.sees sol.extras $ R' a $ (R' (S sol.d₀)).symm $ e $ sol.d y z) := by
    by_contra! this
    have h : sol.d y z ≠ S sol.d₀ := E_ne_SE _ _
    have hdyz := sol.d_invis y z this
    by_cases ha : a = sol.d y z
    all_goals simp [R', h.symm, ha] at hdyz

lemma PartialSolution_with_axioms.invis_lemma'' (sol: PartialSolution_with_axioms) (y z:N) (a:SM) : ¬ (sol.sees sol.extras $ (R' a).symm $ (R' (S sol.d₀)).symm $ e $ sol.d y z) := by
    by_contra! this
    have h : sol.d y z ≠ S sol.d₀ := E_ne_SE _ _
    have h₀ := sol.Sd₀_invis this
    by_cases ha : a = S sol.d₀
    all_goals simp [R', h, ha] at h₀

/- Construction of the new L₀'.  Each L₀'_data object `data` generates a new input-output pair for L₀':  `sol.L₀' (sol.L₀'_pair d₀ d data).1 = (sol.L₀'_pair d₀ d data).2  -/
noncomputable abbrev PartialSolution_with_axioms.L₀'_pair (sol: PartialSolution_with_axioms) (data: L₀'_data sol) : N × N := match data with
  | L₀'_data.iv₁ => (R' (S sol.d₀) sol.x, e sol.d₁)
  | L₀'_data.iv₂ => (R' (S sol.d₀) $ (R' sol.d₀).symm $ e sol.d₁, R' sol.d₀ sol.x)
  | L₀'_data.iii₁ a _ => (R' (S (a - sol.d₀)) sol.y₀, R' (a-sol.d₀) $ (R' (S (sol.S' sol.y₀))).symm $ R' 0 $ sol.L₀' $ R' (sol.S' sol.y₀) sol.x)
  | L₀'_data.iii₂ a _ => (R' (S sol.d₀) $ (R' (a - sol.S' sol.y₀)).symm $ sol.L₀' $ R' (S (a - sol.S' sol.y₀)) sol.x, R' sol.d₀ sol.y₀)
  | L₀'_data.P y z _ => (R' 0 $ R' sol.d₀ y, e (sol.d y z))

lemma PartialSolution_with_axioms.L₀'_no_collide_1  (sol: PartialSolution_with_axioms) (data : L₀'_data sol) : (sol.L₀'_pair data).1 ∉ sol.Dom_L₀' ∧ (sol.L₀'_pair data).2 ∉ sol.Dom_L₀' := by
  rcases data with ⟨⟩ | ⟨⟩ | ⟨a,ha⟩ | ⟨a,ha⟩ | ⟨y,z,hz⟩
  all_goals simp [PartialSolution_with_axioms.L₀'_pair]
  all_goals constructor
  all_goals by_contra! this
  all_goals replace this := (sol.dom_L₀'_involved sol.extras this).1
  . replace this := sol.Sd₀_invis this
    simp [R', sol.noreach_invis (Sfresh_not_in_generators _ _) sol.sees_x] at this
  . replace this := sol.d₁_invis this
    simp [R'] at this
  . replace this := sol.Sd₀_invis this
    simp [R', E_ne_SE] at this
  . replace this := sol.d₀_invis this
    simp [R', sol.noreach_invis (fresh_not_in_generators _ _) sol.sees_x] at this
  . replace this := sol.Sad₀_invis ha this
    simp [R', sol.noreach_invis (sol.Sad₀_noreach ha) sol.sees_y₀] at this
  . replace this := sol.ad₀_invis ha this
    simp [R'] at this
    sorry
  . replace this := sol.Sd₀_invis this
    simp [R'] at this
    sorry
  . replace this := sol.d₀_invis this
    simp [R', sol.noreach_invis (fresh_not_in_generators _ _) sol.sees_y₀] at this
  . replace this := sol.d₀_invis this
    simp [R', sol.noreach_invis (fresh_not_in_generators _ _) (sol.I_involved _ hz).2.1] at this
  replace this := sol.d_invis y z this
  simp only [val_e, ↓reduceIte, one_ne_zero] at this


lemma PartialSolution_with_axioms.nequiv_test {sol: PartialSolution_with_axioms} {a:SM} (ha: ¬ sol.reaches sol.extras a) {y z:N} (hyz: val a y ≠ val a z) : ¬ y ≈ z := by
  sorry

lemma PartialSolution_with_axioms.nequiv_d₀ {sol: PartialSolution_with_axioms} {y z:N} (hyz: val sol.d₀ y ≠ val sol.d₀ z) : ¬ y ≈ z := sol.nequiv_test (fresh_not_in_generators _ _) hyz

lemma PartialSolution_with_axioms.nequiv_d₁ {sol: PartialSolution_with_axioms} {y z:N} (hyz: val sol.d₁ y ≠ val sol.d₁ z) : ¬ y ≈ z := sol.nequiv_test (fresh_not_in_generators _ _) hyz

lemma PartialSolution_with_axioms.nequiv_Sd₀ {sol: PartialSolution_with_axioms} {y z:N} (hyz: val (S sol.d₀) y ≠ val (S sol.d₀) z) : ¬ y ≈ z := sol.nequiv_test (Sfresh_not_in_generators _ _) hyz

lemma PartialSolution_with_axioms.nequiv_d {sol: PartialSolution_with_axioms} (y' z':N) {y z:N} (hyz: val (sol.d y' z') y ≠ val (sol.d y' z') z) : ¬ y ≈ z := sol.nequiv_test (fresh_not_in_generators _ _) hyz

lemma PartialSolution_with_axioms.L₀'_no_collide_2 {sol: PartialSolution_with_axioms} {data data' : L₀'_data sol} (hneq: data ≠ data') : ¬ (sol.L₀'_pair data).1 ≈ (sol.L₀'_pair data').1 ∧ ¬ (sol.L₀'_pair data).2 ≈ (sol.L₀'_pair data').2 := by
  rcases data with ⟨⟩ | ⟨⟩ | ⟨a,ha⟩ | ⟨a,ha⟩ | ⟨y,z,hz⟩
  all_goals rcases data' with ⟨⟩ | ⟨⟩ | ⟨a',ha'⟩ | ⟨a',ha'⟩ | ⟨y',z',hz'⟩
  all_goals try simp at hneq
  all_goals simp [PartialSolution_with_axioms.L₀'_pair, R']
  all_goals constructor
  . apply sol.nequiv_d₀
    sorry
  . apply sol.nequiv_d₁
    sorry
  . apply sol.nequiv_d₀
    sorry
  . apply sol.nequiv_d₁
    sorry
  . apply sol.nequiv_d₀
    sorry
  . apply sol.nequiv_d₁
    sorry
  . apply sol.nequiv_d₀
    sorry
  . apply sol.nequiv_d₁
    sorry
  . apply sol.nequiv_d₁
    sorry
  . apply sol.nequiv_d₀
    sorry
  . apply sol.nequiv_d₁
    sorry
  . apply sol.nequiv_d₀
    sorry
  . apply sol.nequiv_d₁
    sorry
  . sorry
  . apply sol.nequiv_d₁
    sorry
  . apply sol.nequiv_d₀
    sorry
  . apply sol.nequiv_Sd₀
    sorry
  . apply sol.nequiv_d₁
    sorry
  . apply sol.nequiv_d₁
    sorry
  . apply sol.nequiv_d₀
    sorry
  . contrapose! hneq
    sorry
  . contrapose! hneq
    sorry
  . apply sol.nequiv_Sd₀
    sorry
  . apply sol.nequiv_d₀
    sorry
  . apply sol.nequiv_d₀
    sorry
  . apply sol.nequiv_d y' z'
    sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  contrapose! hneq
  sorry

lemma PartialSolution_with_axioms.L₀'_no_collide_3 (sol: PartialSolution_with_axioms) (data data' : L₀'_data sol) : ¬ (sol.L₀'_pair data).1 ≈ (sol.L₀'_pair data').2 := by
  rcases data with ⟨⟩ | ⟨⟩ | ⟨a,ha⟩ | ⟨a,ha⟩ | ⟨y,z,hz⟩
  all_goals rcases data' with ⟨⟩ | ⟨⟩ | ⟨a',ha'⟩ | ⟨a',ha'⟩ | ⟨y',z',hz'⟩
  all_goals simp [PartialSolution_with_axioms.L₀'_pair]
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  sorry

lemma zpow_of_e_inj (a:SM) : Function.Injective (fun n:ℤ ↦ (e a)^n) :=
  injective_zpow_iff_not_isOfFinOrder.mpr (FreeGroup.infinite_order _ (FreeGroup.of_ne_one a))


noncomputable abbrev PartialSolution_with_axioms.L₀'_embed (sol: PartialSolution_with_axioms) : (L₀'_data sol) × ℤ × Bool ↪ N := {
    toFun := fun input ↦ match input with
    | (data, n, true) => (e 0)^n * (sol.L₀'_pair data).1
    | (data, n, false) => (e 0)^n * (sol.L₀'_pair data).2
    inj' := by
      intro (data,n,b) (data',n',b') h
      by_cases hb:b
      . by_cases hb':b'
        . simp [hb, hb'] at h ⊢
          have : (sol.L₀'_pair data).1 ≈ (sol.L₀'_pair data').1 := calc
            _ ≈ (e 0)^n * (sol.L₀'_pair data).1 := rel_of_mul _ n
            _ ≈ (e 0)^n' * (sol.L₀'_pair data').1 := by rw [h]
            _ ≈ _ := Setoid.symm $ rel_of_mul _ n'
          have heq : data = data' := by
            contrapose! this
            exact (sol.L₀'_no_collide_2 this).1
          simp [heq] at h ⊢
          exact zpow_of_e_inj 0 h
        simp [hb, hb'] at h ⊢
        have : (sol.L₀'_pair data).1 ≈ (sol.L₀'_pair data').2 := calc
            _ ≈ (e 0)^n * (sol.L₀'_pair data).1 := rel_of_mul _ n
            _ ≈ (e 0)^n' * (sol.L₀'_pair data').2 := by rw [h]
            _ ≈ _ := Setoid.symm $ rel_of_mul _ n'
        exact sol.L₀'_no_collide_3 _ _ this
      by_cases hb':b'
      . simp [hb, hb'] at h
        simp [hb, hb'] at h ⊢
        have : (sol.L₀'_pair data).2 ≈ (sol.L₀'_pair data').1 := calc
            _ ≈ (e 0)^n * (sol.L₀'_pair data).2 := rel_of_mul _ n
            _ ≈ (e 0)^n' * (sol.L₀'_pair data').1 := by rw [h]
            _ ≈ _ := Setoid.symm $ rel_of_mul _ n'
        exact sol.L₀'_no_collide_3 _ _ $ Setoid.symm this
      simp [hb, hb'] at h ⊢
      have : (sol.L₀'_pair data).2 ≈ (sol.L₀'_pair data').2 := calc
        _ ≈ (e 0)^n * (sol.L₀'_pair data).2 := rel_of_mul _ n
        _ ≈ (e 0)^n' * (sol.L₀'_pair data').2 := by rw [h]
        _ ≈ _ := Setoid.symm $ rel_of_mul _ n'
      have heq : data = data' := by
        contrapose! this
        exact (sol.L₀'_no_collide_2 this).2
      simp [heq] at h ⊢
      exact zpow_of_e_inj 0 h
  }

noncomputable abbrev PartialSolution_with_axioms.L₀'_pre_embed_base (sol: PartialSolution_with_axioms) (input: L₀'_data sol × Bool) : N := match input with
    | (data, true) => (sol.L₀'_pair data).1
    | (data, false) => (sol.L₀'_pair data).2

lemma PartialSolution_with_axioms.L₀'_pre_embed_base_eq (sol: PartialSolution_with_axioms) (data: L₀'_data sol) (b: Bool) : sol.L₀'_pre_embed_base (data, b) = sol.L₀'_embed (data,0,b) := match b with
  | true => by
      simp only [L₀'_pre_embed_base, L₀'_embed, Function.Embedding.coeFn_mk, zpow_zero, one_mul]
  | false => by
      simp only [L₀'_pre_embed_base, L₀'_embed, Function.Embedding.coeFn_mk, zpow_zero, one_mul]

noncomputable abbrev PartialSolution_with_axioms.L₀'_pre_embed (sol: PartialSolution_with_axioms) : L₀'_data sol × Bool ↪ N := {
    toFun := sol.L₀'_pre_embed_base
    inj' := by
      intro (data, b) (data',b') h
      simp only [sol.L₀'_pre_embed_base_eq] at h
      replace h := sol.L₀'_embed.inj' h
      simp only [Prod.mk.injEq, true_and] at h ⊢
      exact h
  }

noncomputable abbrev PartialSolution_with_axioms.L₀'_output  (sol: PartialSolution_with_axioms) : (L₀'_data sol) × ℤ × Bool → N := fun input ↦ match input with
    | (data, n, true) => (e 0)^n * (sol.L₀'_pair data).2
    | (data, n, false) =>  (e 0)^(n-1) * (sol.L₀'_pair data).1

noncomputable abbrev PartialSolution_with_axioms.new_L₀' (sol: PartialSolution_with_axioms) : N → N := sol.L₀'_embed.edit sol.L₀' sol.L₀'_output

lemma PartialSolution_with_axioms.new_L₀'_eval (sol: PartialSolution_with_axioms) (data : L₀'_data sol) : sol.new_L₀' (sol.L₀'_pair data).1 = (sol.L₀'_pair data).2 := by
    convert sol.L₀'_embed.edit_of_attains _ _ ⟨ data, 0, true ⟩
    . simp only [Function.Embedding.coeFn_mk, zpow_zero, one_mul]
    unfold PartialSolution_with_axioms.L₀'_output
    simp only [zpow_zero, one_mul]

lemma PartialSolution_with_axioms.new_L₀'_eval' (sol: PartialSolution_with_axioms) (data : L₀'_data sol) (n:ℤ) : sol.new_L₀' ((e 0)^n * (sol.L₀'_pair data).1) = (e 0)^n * (sol.L₀'_pair data).2 := sol.L₀'_embed.edit_of_attains _ _ ⟨ data, n, true ⟩

lemma PartialSolution_with_axioms.new_L₀'_eval'' (sol: PartialSolution_with_axioms) (data : L₀'_data sol) : sol.new_L₀' (sol.L₀'_pair data).2 = (e 0)⁻¹ * (sol.L₀'_pair data).1 := by
    convert sol.L₀'_embed.edit_of_attains _ _ ⟨ data, 0, false ⟩
    simp only [Function.Embedding.coeFn_mk, zpow_zero, one_mul]

lemma PartialSolution_with_axioms.new_L₀'_eval''' (sol: PartialSolution_with_axioms) (data : L₀'_data sol) (n:ℤ) : sol.new_L₀' ((e 0)^n * (sol.L₀'_pair data).2) = (e 0)^(n-1) * (sol.L₀'_pair data).1 := sol.L₀'_embed.edit_of_attains _ _ ⟨ data, n, false ⟩

lemma PartialSolution_with_axioms.new_L₀'_extend (sol: PartialSolution_with_axioms) {y:N} (hy: y ∈ sol.Dom_L₀') : sol.new_L₀' y = sol.L₀' y := by
    apply sol.L₀'_embed.edit_of_avoids
    intro ⟨ data, n, b ⟩
    by_cases hb:b
    . simp only [hb, Function.Embedding.coeFn_mk, ne_eq]
      by_contra this
      simp [← this, fill_invar'] at hy
      exact (sol.L₀'_no_collide_1 data).1 hy
    simp only [hb, Function.Embedding.coeFn_mk, ne_eq]
    by_contra this
    simp only [← this, fill_invar'] at hy
    exact (sol.L₀'_no_collide_1 data).2 hy

noncomputable abbrev PartialSolution_with_axioms.new_predom (sol : PartialSolution_with_axioms) : Finset N := sol.L₀'_pre_embed.range_finset

lemma PartialSolution_with_axioms.mem_new_predom (sol : PartialSolution_with_axioms) (data : L₀'_data sol): (sol.L₀'_pair data).1 ∈ sol.new_predom := by
    rw [sol.L₀'_pre_embed.in_range_iff_attains]
    exact sol.L₀'_pre_embed.attains_image (data, true)

lemma PartialSolution_with_axioms.mem_new_predom' (sol : PartialSolution_with_axioms) (data : L₀'_data sol): (sol.L₀'_pair data).2 ∈ sol.new_predom := by
    rw [sol.L₀'_pre_embed.in_range_iff_attains]
    exact sol.L₀'_pre_embed.attains_image (data, false)

/- Construction of the new `op`.  Each op_data object `data` produces an instance of the operation `op`: `sol.op (op_triple d₀ d data).1 (op_triple d₀ d data).2.1 = (op_triple d₀ d data).2.2. -/
noncomputable abbrev PartialSolution_with_axioms.op_triple (sol : PartialSolution_with_axioms) : op_data sol → N × N × M := fun data ↦ match data with
  | op_data.old y z _hop => (y, z, sol.op y z)
  | op_data.v => (sol.x, sol.x, Sum.inl sol.d₀)
  | op_data.P₁ y z _hI => (z, sol.x, Sum.inr $ (R' (S sol.d₀)).symm $ e $ sol.d y z)
  | op_data.P₂ y z _hI _hz => ((R' (S sol.d₀)).symm $ e $ sol.d y z, z, Sum.inr $ (R' (S (sol.S' z))).symm $ sol.L₀' $ R' 0 $ R' (sol.S' z) x)

noncomputable abbrev PartialSolution_with_axioms.op_embed (sol : PartialSolution_with_axioms) : op_data sol ↪ N × N := {
    toFun := fun data ↦ ((sol.op_triple data).1, (sol.op_triple data).2.1)
    inj' := by
      have hxx : (x,x) ∉ sol.Dom_op := by
        by_contra! hxx
        exact hx (sol.axiom_v'' _ hxx).1

      intro data data' h
      rcases data with ⟨ y,z,hop ⟩ | ⟨⟩ | ⟨ y,z,hI ⟩ | ⟨ y,z,hI,hz⟩
      . rcases data' with ⟨ y',z',hop' ⟩ | ⟨⟩ | ⟨ y',z',hI' ⟩ | ⟨ y',z',hI',hz'⟩
        all_goals simp [PartialSolution_with_axioms.op_triple] at h ⊢
        . exact h
        . rw [h.1,h.2] at hop; exact hxx hop
        . exact (h.1 ▸ (sol.axiom_P x y' z' hI').2.1) (h.2 ▸ hop)
        exact h.1 ▸ sol.invis_lemma y' z' $ (sol.dom_op_involved sol.extras hop).1
      . rcases data' with ⟨ y',z',hop' ⟩ | ⟨⟩ | ⟨ y',z',hI' ⟩ | ⟨ y',z',hI',hz'⟩
        all_goals simp [PartialSolution_with_axioms.op_triple] at h ⊢
        . rw [←h.1,←h.2] at hop'; exact hxx hop'
        . exact (sol.axiom_P _ _ _ hI').2.2.1 h.symm
        exact hx $ h.2 ▸ hz'
      . rcases data' with ⟨ y',z',hop' ⟩ | ⟨⟩ | ⟨ y',z',hI' ⟩ | ⟨ y',z',hI',hz'⟩
        all_goals simp [PartialSolution_with_axioms.op_triple] at h ⊢
        . rw [←h.1, ←h.2] at hop'
          exact (sol.axiom_P _ _ _ hI).2.1 hop'
        . exact (sol.axiom_P _ _ _ hI).2.2.1 h
        . exact ⟨ sol.axiom_P' _ _ _ _ hI (h ▸ hI'), h ⟩
        exact (sol.axiom_P _ _ _ hI').2.2.1 h.2.symm
      rcases data' with ⟨ y',z',hop' ⟩ | ⟨⟩ | ⟨ y',z',hI' ⟩ | ⟨ y',z',hI',hz'⟩
      all_goals simp [PartialSolution_with_axioms.op_triple] at h ⊢
      . exact h.1 ▸ sol.invis_lemma y z $ (sol.dom_op_involved sol.extras hop').1
      . exact hx $ h.2 ▸ hz
      . exact (sol.axiom_P _ _ _ hI).2.2.1 h.2
      exact sol.d_injective $ FreeGroup.of_injective h.1
  }

noncomputable abbrev PartialSolution_with_axioms.op_output (sol : PartialSolution_with_axioms): op_data sol → M := fun data ↦ (sol.op_triple data).2.2

noncomputable abbrev PartialSolution_with_axioms.new_op (sol : PartialSolution_with_axioms) : N → N → M := fun y ↦ (fun z ↦ sol.op_embed.edit (fun (y,z) ↦ sol.op y z) sol.op_output (y,z))

lemma PartialSolution_with_axioms.op_eval (sol : PartialSolution_with_axioms) (data : op_data sol) : sol.new_op (sol.op_triple data).1 (sol.op_triple data).2.1 = (sol.op_triple data).2.2 := sol.op_embed.edit_of_attains _ _ data

lemma PartialSolution_with_axioms.op_extend (sol : PartialSolution_with_axioms) {y:N} {z:N} (h: (y,z) ∈ sol.Dom_op) : sol.new_op y z = sol.op y z := sol.op_embed.edit_of_attains _ _ (op_data.old y z h)

noncomputable abbrev PartialSolution_with_axioms.new_dom_op (sol : PartialSolution_with_axioms) : Finset (N × N) := sol.op_embed.range_finset

lemma PartialSolution_with_axioms.mem_new_dom_op (sol : PartialSolution_with_axioms) (data : op_data sol) : ((sol.op_triple data).1, (sol.op_triple data).2.1) ∈ sol.new_dom_op := (sol.op_embed.in_range_iff_attains _).mpr $ sol.op_embed.attains_image data

/- Construction of the new I.  Each I_data object `data` produces a triple for I. -/
noncomputable abbrev PartialSolution_with_axioms.I_triple (sol : PartialSolution_with_axioms) : I_data sol ↪ N × N × N := {
    toFun := fun data ↦ match data with
      | I_data.old x' y z hI hxx' => (x',y,z)
      | I_data.P₁ y z hI hz => (z,x,(R' (S sol.d₀)).symm $ e $ sol.d y z)
      | I_data.P₂ y z hI hz => ((R' (S sol.d₀)).symm $ e $ sol.d y z, z, (R' (S (sol.S' z))).symm $ sol.L₀' $ R' 0 $ R' (sol.S' z) x)
    inj' := by
      intro data data' h
      rcases data with ⟨ x',y,z,hI, hxx'⟩ | ⟨y,z,hI,hz⟩ | ⟨y,z,hI,hz⟩
      . rcases data' with ⟨ x'',y',z',hI', hxx''⟩ | ⟨y',z',hI',hz'⟩ | ⟨y',z',hI',hz'⟩
        all_goals simp at h ⊢
        . exact h
        . exact h.2.2 ▸ sol.invis_lemma y' z' $ (sol.I_involved sol.extras hI).2.2
        exact h.1 ▸ sol.invis_lemma y' z' $ (sol.I_involved sol.extras hI).1
      . rcases data' with ⟨ x'',y',z',hI', hxx''⟩ | ⟨y',z',hI',hz'⟩ | ⟨y',z',hI',hz'⟩
        all_goals simp at h ⊢
        . exact h.2.2 ▸ sol.invis_lemma y z $ (sol.I_involved sol.extras hI').2.2
        . exact sol.d_injective $ FreeGroup.of_injective h.2
        exact h.1 ▸ sol.invis_lemma y' z' $ (sol.I_involved sol.extras hI).2.2
      rcases data' with ⟨ x'',y',z',hI', hxx''⟩ | ⟨y',z',hI',hz'⟩ | ⟨y',z',hI',hz'⟩
      all_goals simp at h ⊢
      . exact h.1 ▸ sol.invis_lemma y z $ (sol.I_involved sol.extras hI').1
      . exact h.1 ▸ sol.invis_lemma y z $ (sol.I_involved sol.extras hI').2.2
      exact sol.d_injective $ FreeGroup.of_injective h.1
  }

noncomputable abbrev PartialSolution_with_axioms.new_I (sol : PartialSolution_with_axioms) : Finset (N × N × N) := sol.I_triple.range_finset

-- Set up S

noncomputable abbrev PartialSolution_with_axioms.new_S (sol : PartialSolution_with_axioms) : N → SM := fun y ↦ if y=x then sol.d₀ else sol.S' y

lemma PartialSolution_with_axioms.new_S_x (sol : PartialSolution_with_axioms) : sol.new_S x = sol.d₀ := by simp only [↓reduceIte, new_S]

lemma PartialSolution_with_axioms.new_S_extend (sol : PartialSolution_with_axioms) {y:N} (h: y ∈ sol.Dom_S') : sol.new_S y = sol.S' y := by
    by_cases hy : y = x
    . rw [hy] at h
      contrapose! h
      exact sol.hx
    simp only [hy, ↓reduceIte, new_S]

lemma PartialSolution_with_axioms.new_S_y₀ (sol : PartialSolution_with_axioms) (h: x ≠ 1): sol.new_S sol.y₀ = sol.S' sol.y₀ := sol.new_S_extend $ hind sol.y₀ $ parent_lt h


open PartialSolution_with_axioms

lemma enlarge_S'_induction_with_axioms (sol : PartialSolution_with_axioms) : ∃ sol' : PartialSolution, sol.toPartialSolution ≤ sol' ∧ sol.x ∈ sol'.Dom_S' := by
  classical

  have hxa := sol.hx

  let sol' : PartialSolution := {
    L₀' := sol.new_L₀'
    op := sol.new_op
    S' := sol.new_S
    I := sol.new_I
    Predom_L₀' := sol.Predom_L₀' ∪ sol.new_predom
    Dom_op := sol.new_dom_op
    Dom_S' := sol.Dom_S' ∪ {x}
    axiom_i'' := by
      intro x' y hx' hxy n
      simp only [Finset.mem_union] at hx'
      simp only [fill_union, ← hxy, Set.mem_union]
      rcases hx' with hx' | hx'
      . simp only [sol.new_L₀'_extend (mem_fill hx')] at hxy ⊢
        obtain ⟨ h1, h2, h3 ⟩ := sol.axiom_i'' x' (sol.L₀' x') hx' (by rfl) n
        simp only [h1, true_or, sol.new_L₀'_extend $ (fill_invar' _ _ n).mpr $ mem_fill hx', h2,
          sol.new_L₀'_extend $ (fill_invar' _ _ n).mpr h1, h3, and_self]
      rw [sol.L₀'_pre_embed.in_range_iff_attains] at hx'
      obtain ⟨ ⟨ data, b ⟩, hdata ⟩ := hx'
      simp only [← hdata]
      by_cases h:b
      . simp only [h, Function.Embedding.coeFn_mk, sol.new_L₀'_eval, mem_fill $ sol.mem_new_predom' _,
        or_true, sol.new_L₀'_eval', sol.new_L₀'_eval''', and_self]
      simp only [h, Function.Embedding.coeFn_mk, sol.new_L₀'_eval'']
      group
      simp only [Int.reduceNeg, zpow_one, new_L₀'_eval''', mul_left_inj, sol.new_L₀'_eval', and_true]
      refine ⟨ Or.inr $ (fill_invar' _ _ _).mpr $ mem_fill $ sol.mem_new_predom data, ?_ ⟩
      convert sol.new_L₀'_eval''' data n using 3
      exact neg_add_eq_sub 1 n

    axiom_S := by
      intro x' y hx' hyx
      simp only [Finset.mem_union, Finset.mem_singleton] at hx'
      rcases hx' with hx' | hx'
      . exact Finset.mem_union_left _ $ sol.axiom_S x' y hx' hyx
      rw [hx', le_iff_lt_or_eq] at hyx
      rcases hyx with hyx | hyx
      . exact Finset.mem_union_left _ $ hind y hyx
      simp only [hyx, Finset.mem_union, Finset.mem_singleton, or_true]
    axiom_iii'' := by
      intro x' y a hx' hy hray
      have hneq : x' ≠ y := by
        rw [←hray]
        exact (R'_axiom_iib a x').symm
      simp only [Finset.mem_union, Finset.mem_singleton] at hx' hy
      rcases hx' with hx' | hx'
      . rcases hy with hy | hy
        . obtain ⟨ h1, h2, h3 ⟩ := sol.axiom_iii'' x' y a hx' hy hray
          simp only [fill_union, sol.new_S_extend hx', Set.mem_union, h1, true_or, sol.new_S_extend hy,
            sol.new_L₀'_extend h1, h2, sol.new_L₀'_extend h2, h3, and_self]
        rw [hy] at hray hneq ⊢
        have : x' = sol.y₀ := by
          rcases hray ▸ (parent_of_adjacent $ R'_adjacent a x') with this | this
          . exact this
          contrapose! hxa
          exact sol.axiom_S x' sol.x hx' $ this ▸ (parent_le x')
        have hneq' : sol.x ≠ 1 := by
          contrapose! hneq
          unfold PartialSolution_with_axioms.y₀ at this
          simp only [this, hneq, parent_one]
        rw [this] at hray ⊢
        replace hB := hB a hray.symm
        have h1 := sol.mem_new_predom $ L₀'_data.iii₂ a hray.symm
        unfold PartialSolution.Dom_L₀' at hB
        simp only [fill_union, sol.new_S_y₀ hneq', Set.mem_union, hB, true_or, sol.new_S_x,
          sol.new_L₀'_extend hB, mem_fill h1, or_true, sol.new_L₀'_eval (L₀'_data.iii₂ a hray.symm),
          Equiv.symm_apply_apply, and_self, y₀]
      rcases hy with hy | hy
      . rw [hx'] at hray hneq ⊢
        have : y = sol.y₀ := by
          rcases hray ▸ (parent_of_adjacent $ R'_adjacent a x) with this | this
          . contrapose! hxa
            exact sol.axiom_S y x hy $ this ▸ (parent_le y)
          exact this
        have hneq' : x ≠ 1 := by
          contrapose! hneq
          simp only [this, hneq, parent_one, y₀]
        rw [this] at hray ⊢
        replace hA := hA a hray
        have h1 := sol.mem_new_predom $ L₀'_data.iii₁ a hray
        unfold PartialSolution.Dom_L₀' at hA
        unfold PartialSolution_with_axioms.L₀'_pair at h1
        have hfill : (sol.L₀' $ R' (sol.S' sol.y₀) sol.x) ∈ fill sol.Predom_L₀' := sol.R0_mem_L₀' hA
        have heval : (sol.new_L₀' $ R' 0 $ sol.L₀' $ R' (sol.S' sol.y₀) sol.x) = R' (sol.S' sol.y₀) sol.x := by
          rw [sol.new_L₀'_extend $ (R0_mem_fill_iff _ _).mpr hfill]
          exact PartialSolution.inv_L₀' hA
        simp only [fill_union, sol.new_S_x, Set.mem_union, mem_fill h1, sol.new_S_y₀ hneq', sol.new_L₀'_eval (L₀'_data.iii₁ a hray), Equiv.symm_apply_apply, Equiv.apply_symm_apply, true_and, true_or, or_true, y₀, hfill, heval, R0_mem_fill_iff]
      contrapose! hneq
      rw [hx',hy]
    axiom_iv'' := by
      intro x' hx'
      simp only [Finset.mem_union, Finset.mem_singleton] at hx'
      rcases hx' with hx' | hx'
      . obtain ⟨ h1, h2, h3 ⟩ := sol.axiom_iv'' x' hx'
        simp only [fill_union, sol.new_S_extend hx', Set.mem_union, sol.new_L₀'_extend h1, sol.new_L₀'_extend h2, h3, and_true]
        exact ⟨Or.inl h1, Or.inl h2⟩
      simp only [hx', sol.new_L₀'_eval L₀'_data.iv₁, sol.new_L₀'_eval L₀'_data.iv₂, Equiv.symm_apply_apply, and_true, sol.new_S_x]
      exact ⟨ mem_fill $ Finset.mem_union_right _ $ sol.mem_new_predom L₀'_data.iv₁, mem_fill $ Finset.mem_union_right _ $ sol.mem_new_predom L₀'_data.iv₂ ⟩
    axiom_v'' := by
      intro x' hx'
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, new_dom_op, Function.Embedding.in_range_iff_attains, Function.Embedding.attains] at hx'
      obtain ⟨ data, h ⟩  := hx'
      cases data with
      | old y z hop =>
        simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at h
        rw [h.1,h.2] at hop
        obtain ⟨ h3, h4 ⟩ := sol.axiom_v'' x' hop
        have hxne : x' ≠ x := by
          contrapose! hxa
          rwa [hxa] at h3
        simp only [Finset.mem_union, h3, Finset.mem_singleton, hxne, or_false, ↓reduceIte, h4, sol.new_S_extend h3,
          true_and, sol.op_extend hop]
      | v =>
        simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq, and_self] at h
        simp only [← h, Finset.mem_union, Finset.mem_singleton, or_true, true_and, sol.op_eval op_data.v, sol.new_S_x]
      | P₁ y z hI =>
        simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at h
        simp only [← h.2, Finset.mem_union, Finset.mem_singleton, or_true, true_and, sol.op_eval op_data.v, sol.new_S_x]
      | P₂ y z hI hz =>
        simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at h
        rw [<-h.2] at h
        exfalso
        exact (h.1 ▸ (sol.invis_lemma y z)) (sol.dom_S'_involved sol.extras hz).1

    axiom_vi'' := by
      intro y a hya
      simp only [sol.op_embed.in_range_iff_attains] at hya
      obtain ⟨ data, h ⟩ := hya
      cases data with
      | old y' z' hop =>
        simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at h
        rw [h.1, h.2] at hop
        have := sol.axiom_vi'' y a hop
        simp only [Finset.mem_union, this.1, Finset.mem_singleton, true_or, sol.op_extend hop, this.2,
          sol.new_S_extend this.1, and_self]
      | v =>
        simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at h
        exfalso
        exact (h.1 ▸ (R'_axiom_iib a y)) h.2
      | P₁ y' z' hI =>
        simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at h
        rw [h.1, ←h.2] at hI
        have := (sol.axiom_P _ _ _ hI).2.2.2.1 a
        contrapose! this
        rfl
      | P₂ y' z' hI hz =>
        simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at h
        rw [h.2] at hz
        replace h := congrArg (R' a).symm $ h.2 ▸ h.1
        simp only [R', Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, inv_mul_cancel_left] at h
        rw [←h] at hz
        replace hz := (sol.dom_S'_involved sol.extras hz).1
        contrapose! hz
        exact sol.invis_lemma'' y' y a
    axiom_vii'' := by
      intro x' y hneq hray hop
      simp only [sol.op_embed.in_range_iff_attains] at hop
      obtain ⟨ data, h ⟩ := hop
      cases data with
      | old y' z hop =>
        simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at h
        rw [h.1, h.2] at hop
        obtain ⟨ z', h1, h2 ⟩ := sol.axiom_vii'' x' y hneq hray hop
        use z'
        simp only [sol.op_extend hop, h1, Finset.mem_union, Finset.mem_singleton, fill_union,
          Set.mem_union, R0_mem_fill_iff, true_and]
        rcases h2 with h2 | ⟨ h2, h3, h4, h5 ⟩
        . by_cases hxx' : x = x'
          . right
            rw [← hxx'] at h1 h2 ⊢
            simp only [or_true, sol.new_S_x, true_and]
            refine ⟨ sol.mem_new_dom_op $ op_data.P₁ y z' h2, ?_, ?_ ⟩
            . right
              have := mem_fill $ sol.mem_new_predom $ L₀'_data.P y z' h2
              simp only [R0_mem_fill_iff] at this
              exact this
            simp only [sol.op_eval $ op_data.P₁ y z' h2, sol.new_L₀'_eval $ L₀'_data.P y z' h2]
          left
          convert sol.I_triple.attains_in_range $ I_data.old x' y z' h2 hxx'
        right
        simp only [sol.mem_new_dom_op $ op_data.old z' x' h2, h3, true_or, sol.new_S_extend h3,
          (R0_mem_fill_iff _ _).mp h4, sol.op_extend h2, h5, sol.new_L₀'_extend h4, and_self]
      | v =>
        simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at h
        rw [← h.1, ← h.2] at hneq
        contrapose! hneq
        rfl
      | P₁ y' z hI =>
        simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq, op_embed] at h
        use (R' (S sol.d₀)).symm $ e $ sol.d y' z
        simp only [← h.1, ← h.2, sol.op_eval $ op_data.P₁ y' z hI, Finset.mem_union,
          Finset.mem_singleton, fill_union, Set.mem_union, R0_mem_fill_iff, true_and]
        by_cases hz : z ∈ sol.Dom_S'
        . right
          replace hC := hC y' z hI hz
          simp only [sol.mem_new_dom_op $ op_data.P₂ y' z hI hz, hz, true_or, sol.new_S_extend hz,
            (R0_mem_fill_iff _ _).mp hC, sol.op_eval $ op_data.P₂ y' z hI hz, sol.new_L₀'_extend hC,
            and_self]
        left
        exact sol.I_triple.attains_in_range $ I_data.P₁ y' z hI hz
      | P₂ y' z hI hz =>
        simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at h
        rw [h.2] at hz hI h
        use (R' (S (sol.S' y))).symm $ sol.L₀' $ R' 0 $ R' (sol.S' y) sol.x
        simp only [← h.1, sol.op_eval $ op_data.P₂ y' y hI hz, Finset.mem_union, Finset.mem_singleton,
          fill_union, Set.mem_union, R0_mem_fill_iff, true_and]
        left
        exact sol.I_triple.attains_in_range $ I_data.P₂ y' y hI hz
    axiom_P := by
      intro x' y z hI
      obtain ⟨ data, hdata ⟩ := (sol.I_triple.in_range_iff_attains _).mp hI
      cases data with
      | old x'' y' z' hI' hxx' =>
        simp only [ne_eq, Function.Embedding.coeFn_mk, Prod.mk.injEq] at hdata
        simp only [hdata.1, hdata.2.1, hdata.2.2] at hI' hxx'
        have := sol.axiom_P x' y z hI'
        simp only [Finset.mem_union, this.1, Finset.mem_singleton, false_or, ne_eq, this.2.2.1,
          not_false_eq_true, this.2.2.2, implies_true, and_self, and_true]
        constructor
        . contrapose! hxx'
          exact hxx'.symm
        by_contra hop
        obtain ⟨ opdata, h ⟩ := (sol.op_embed.in_range_iff_attains _).mp hop
        cases opdata with
        | old y'' z'' hop' =>
          simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at h
          rw [h.1, h.2] at hop'
          exact this.2.1 hop'
        | v =>
          simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at h
          simp only [← h.2, ← h.1, ne_eq, not_true_eq_false, false_and, and_false] at this
        | P₁ y'' z'' hI'' =>
          simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at h
          exact hxx' h.2
        | P₂ y'' z'' hI'' hz' =>
          simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at h
          rw [h.2] at hz'
          exact this.1 hz'
      | P₁ y' z' hI hz =>
        simp only [ne_eq, Function.Embedding.coeFn_mk, Prod.mk.injEq] at hdata
        simp only [← hdata.2.2, hdata.1] at hz hI ⊢
        have := sol.axiom_P x y' x' hI
        refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_ ⟩
        . simp only [Finset.mem_union, hz, Finset.mem_singleton, this.2.2.1,
          or_self, not_false_eq_true]
        . by_contra hop
          obtain ⟨ opdata, h ⟩ := (sol.op_embed.in_range_iff_attains _).mp hop
          cases opdata with
          | old y'' z'' hop' =>
            simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at h
            rw [h.1, h.2] at hop'
            exact sol.invis_lemma y' x' (sol.dom_op_involved sol.extras hop').1
          | v =>
            simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at h
            simp only [← h.2, ne_eq, not_true_eq_false, false_and, and_false] at this
          | P₁ y'' z'' hI'' =>
            simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at h
            exact this.2.2.1 h.2.symm
          | P₂ y'' z'' hI'' hz' =>
            simp [Function.Embedding.coeFn_mk, Prod.mk.injEq] at h
            rw [h.2] at hz'
            exact hz hz'
        . replace hI := (sol.I_involved sol.extras hI).2.2
          by_contra h
          rw [←h] at hI
          exact sol.invis_lemma y' x' hI
        . intro a
          replace hI := (sol.I_involved sol.extras hI).2.2
          contrapose! hI
          apply_fun (R' a).symm at hI
          simp only [R', Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, inv_mul_cancel_left] at hI
          rw [<-hI]
          exact sol.invis_lemma'' y' x' a
        . sorry
        sorry
      | P₂ y' z' hI hz =>
        simp only [ne_eq, Function.Embedding.coeFn_mk, Prod.mk.injEq] at hdata
        simp [← hdata.1, ← hdata.2]
        have hinvis := sol.invis_lemma y' z'
        refine ⟨ ⟨ ?_, ?_ ⟩, ?_, ?_, ?_, ?_, ?_ ⟩
        . contrapose! hinvis
          exact (sol.dom_S'_involved sol.extras hinvis).1
        . contrapose! hinvis
          rw [hinvis]
          apply sol.extras_involved sol.extras
          simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
        . contrapose! hinvis
          unfold Function.Embedding.attains at hinvis
          obtain ⟨ opdata, h ⟩ := hinvis
          cases opdata with
          | old y'' z'' hop' =>
            simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at h
            rw [h.1, h.2] at hop'
            exact (sol.dom_op_involved sol.extras hop').2.1
          | v =>
            simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at h
            rw [← h.2]
            exact sol.extras_involved sol.extras sol.x_in_extras
          | P₁ y'' z'' hI'' =>
            simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at h
            rw [← h.2]
            exact sol.extras_involved sol.extras sol.x_in_extras
          | P₂ y'' z'' hI'' hz' =>
            simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at h
            rw [h.2] at hz'
            exact (sol.dom_S'_involved sol.extras hz').1
        . contrapose! hinvis
          rw [←hinvis]
          exact sol.sees_R'_inv (sol.reaches_S $ sol.reaches_involved (sol.dom_S'_involved sol.extras hz).2) (sol.dom_L₀'_involved sol.extras $ hC y' z' hI hz).2
        . intro a
          have hinvis' := sol.invis_lemma' y' z' a
          contrapose! hinvis'
          rw [←hinvis']
          exact sol.sees_R'_inv (sol.reaches_S $ sol.reaches_involved (sol.dom_S'_involved sol.extras hz).2) (sol.dom_L₀'_involved sol.extras $ hC y' z' hI hz).2
        . sorry
        sorry
    axiom_P' := by
      intro x' y y' z hy hy'
      obtain ⟨ data, hy ⟩ := (sol.I_triple.in_range_iff_attains _).mp hy
      obtain ⟨ data', hy' ⟩ := (sol.I_triple.in_range_iff_attains _).mp hy'
      cases data with
      | old x'' y'' z'' hI' hxx' =>
        simp only [ne_eq, Function.Embedding.coeFn_mk, Prod.mk.injEq] at hy
        simp only [hy.1, hy.2.1, hy.2.2] at hI' hxx'
        cases data' with
        | old x''' y''' z''' hI'' hxx'' =>
          simp only [ne_eq, Function.Embedding.coeFn_mk, Prod.mk.injEq] at hy'
          simp only [hy'.1, hy'.2.1, hy'.2.2] at hI'' hxx''
          exact sol.axiom_P' x' y y' z hI' hI''
        | P₁ y''' z''' hI'' hz' =>
          simp only [ne_eq, Function.Embedding.coeFn_mk, Prod.mk.injEq] at hy'
          simp only [hy'.1, hy'.2.1, hy'.2.2] at hI'' hz'
          exfalso
          exact sol.invis_lemma y''' z''' (hy'.2.2 ▸ (sol.I_involved sol.extras hI').2.2)
        | P₂ y''' z''' hI'' hz' =>
          simp only [ne_eq, Function.Embedding.coeFn_mk, Prod.mk.injEq] at hy'
          simp only [hy'.1, hy'.2.1, hy'.2.2] at hI'' hz'
          exfalso
          exact sol.invis_lemma y''' z''' (hy'.1 ▸ (sol.I_involved sol.extras hI').1)
      | P₁ y'' z'' hI' hz =>
        simp only [ne_eq, Function.Embedding.coeFn_mk, Prod.mk.injEq] at hy
        simp only [hy.1, hy.2.1, hy.2.2] at hI' hz
        cases data' with
        | old x''' y''' z''' hI'' hxx'' =>
          simp only [ne_eq, Function.Embedding.coeFn_mk, Prod.mk.injEq] at hy'
          simp only [hy'.1, hy'.2.1, hy'.2.2] at hI'' hxx''
          exfalso
          exact sol.invis_lemma y'' z'' (hy.2.2 ▸ (sol.I_involved sol.extras hI'').2.2)
        | P₁ y''' z''' hI'' hz' =>
          simp only [ne_eq, Function.Embedding.coeFn_mk, Prod.mk.injEq] at hy'
          simp only [hy'.1, hy'.2.1, hy'.2.2] at hI'' hz'
          rw [←hy.2.1, ←hy'.2.1]
        | P₂ y''' z''' hI'' hz' =>
          simp only [ne_eq, Function.Embedding.coeFn_mk, Prod.mk.injEq] at hy'
          simp only [hy'.1, hy'.2.1, hy'.2.2] at hI'' hz'
          exfalso
          exact sol.invis_lemma y''' z''' (hy'.1 ▸ (sol.I_involved sol.extras hI').2.2)
      | P₂ y'' z'' hI' hz =>
        simp only [ne_eq, Function.Embedding.coeFn_mk, Prod.mk.injEq] at hy
        simp only [hy.1, hy.2.1, hy.2.2] at hI' hz
        cases data' with
        | old x''' y''' z''' hI'' hxx'' =>
          simp only [ne_eq, Function.Embedding.coeFn_mk, Prod.mk.injEq] at hy'
          simp only [hy'.1, hy'.2.1, hy'.2.2] at hI'' hxx''
          exfalso
          exact sol.invis_lemma y'' z'' (hy.1 ▸ (sol.I_involved sol.extras hI'').1)
        | P₁ y''' z''' hI'' hz' =>
          simp only [ne_eq, Function.Embedding.coeFn_mk, Prod.mk.injEq] at hy'
          simp only [hy'.1, hy'.2.1, hy'.2.2] at hI'' hz'
          exfalso
          exact sol.invis_lemma y'' z'' (hy.1 ▸ (sol.I_involved sol.extras hI'').2.2)
        | P₂ y''' z''' hI'' hz' =>
          simp only [ne_eq, Function.Embedding.coeFn_mk, Prod.mk.injEq] at hy'
          simp only [hy'.1, hy'.2.1, hy'.2.2] at hI'' hz'
          rw [←hy.2.1, ←hy'.2.1]
          have := hy.1 ▸ hy'.1
          simp only [EmbeddingLike.apply_eq_iff_eq] at this
          replace this := sol.d_injective $ FreeGroup.of_injective this
          rw [this.2]
    axiom_L := by
      sorry
  }

  refine ⟨ sol', ?_, ?_ ⟩
  . refine ⟨ Finset.subset_union_left, ?_, Finset.subset_union_left, ?_, ?_, ?_ ⟩
    . intro y hy
      exact sol.mem_new_dom_op $ op_data.old y.1 y.2 hy
    . intro _ hy
      exact (sol.new_L₀'_extend hy).symm
    . intro _ hxy
      exact (sol.op_extend hxy).symm
    intro y hy
    exact (sol.new_S_extend hy).symm
  simp only [Finset.mem_union, Finset.mem_singleton, or_true, sol']

lemma enlarge_S'_induction {sol : PartialSolution} {x:N} (hind: ∀ y:N, y < x → y ∈ sol.Dom_S') : ∃ sol', sol ≤ sol' ∧ x ∈ sol'.Dom_S' := by sorry

-- derive this from the inductive step `enlarge_S'_induction` using the API for ordering on `N` in `SmallMagma.lean`

lemma enlarge_S' (sol : PartialSolution) (x:N) : ∃ sol', sol ≤ sol' ∧ x ∈ sol'.Dom_S' := by sorry

lemma enlarge_op (sol : PartialSolution) (x y :N) : ∃ sol', sol ≤ sol' ∧ (x,y) ∈ sol'.Dom_op := by
  wlog hx : x ∈ sol.Dom_S'
  . obtain ⟨ sol', hsol, hx ⟩ := enlarge_S' sol x
    obtain ⟨ sol'', hsol', hx' ⟩ := this sol' x y hx
    exact ⟨ sol'', hsol.trans hsol', hx' ⟩
  wlog hy : y ∈ sol.Dom_S'
  . obtain ⟨ sol', hsol, hy ⟩ := enlarge_S' sol y
    obtain ⟨ sol'', hsol', hy' ⟩ := this sol' x y (hsol.2.2.1 hx) hy
    exact ⟨ sol'', hsol.trans hsol', hy' ⟩
  set w := R' 0 $ R' (sol.S' x) $ y
  wlog hw : w ∈ sol.Dom_L₀'
  . obtain ⟨ sol', hsol, hw ⟩ := enlarge_L₀' sol w
    obtain ⟨ sol'', hsol', hw' ⟩ := this sol' x y (hsol.2.2.1 hx) (hsol.2.2.1 hy) ((hsol.2.2.2.2.2 x hx) ▸ hw)
    exact ⟨ sol'', hsol.trans hsol', hw' ⟩

  have no_pending : ¬ ∃ z, (y,z,x) ∈ sol.I := by
    by_contra this
    obtain ⟨ z, hz ⟩ := this
    have := sol.axiom_P y z x hz
    exact this.1 hy
  by_cases hdef : (x,y) ∈ sol.Dom_op
  . exact ⟨ sol, sol.refl, hdef ⟩
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
          rw [←h2] at h1
          simp only [R', Equiv.coe_fn_mk, mul_left_eq_self, FreeGroup.of_ne_one] at h1
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

        obtain ⟨ z, h1, h2 ⟩ := sol.axiom_vii'' x' y' hxy' hxay hop'
        rcases h2 with h2 | ⟨ h3, h4, h5 ⟩
        . use z
          simp only [hne, ↓reduceIte, h1, h2, Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq,
            true_or, and_self]
        have hzne : ¬ (z = x ∧ x' = x) := by
          by_contra hzne
          rw [hzne.1, hzne.2] at h3
          exact hdef h3
        simp only [hne, ↓reduceIte, Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq]
        refine ⟨z, h1, Or.inr ⟨ Or.inl h3, h4, ?_ ⟩ ⟩
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
      axiom_P' := sol.axiom_P'
      axiom_L := sol.axiom_L
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
          rw [←hxy.1, ←hxy.2]
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
        obtain ⟨ z, h3, h4 ⟩ := sol.axiom_vii'' x' y' hxy' hneq h2
        refine ⟨ z, h3, ?_ ⟩
        rcases h4 with h4 | ⟨ h5, h6, h7 ⟩
        . exact Or.inl h4
        refine Or.inr ⟨ Or.inl h5, h6, ?_ ⟩
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
        exact h3.2.1 a h4
      axiom_P' := sol.axiom_P'
      axiom_L := sol.axiom_L
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

  set d0 := E $ sol.fresh_generator {x,y,w} 0
  set z := (e d0)^2
  have hz_invis : ¬ sol.sees {x, y, w} z := sol.fresh_invis_pow {x, y, w} 0 (Ne.symm (Nat.zero_ne_add_one 1))
  have hz_invis' : ¬ sol.sees {x, y, w} (e d0) := sol.fresh_invis {x, y, w} 0
  classical
  set z' := (R' (S (sol.S' x))).symm $ sol.L₀' w
  set sol' : PartialSolution := {
    L₀' := sol.L₀'
    op := fun x' y' ↦ if (x',y') = (x,y) then Sum.inr $ z else if (x',y') = (z,x) then Sum.inr z' else sol.op x' y'
    S' := sol.S'
    Predom_L₀' := sol.Predom_L₀'
    Dom_op := sol.Dom_op ∪ { (x,y), (z, x) }
    Dom_S' := sol.Dom_S'
    I := sol.I ∪ {(z,x,z')}
    axiom_i'' := sol.axiom_i''
    axiom_S := sol.axiom_S
    axiom_iii'' := sol.axiom_iii''
    axiom_iv'' := sol.axiom_iv''
    axiom_v'' := by
      intro x' hx'
      simp only [Finset.union_insert, Finset.mem_insert, Prod.mk.injEq, Finset.mem_union,
        Finset.mem_singleton] at hx'
      rcases hx' with hx' | hx' | hx'
      . rw [←hx'.1, ←hx'.2] at hxy
        contrapose! hxy
        rfl
      . obtain ⟨ h1, h2 ⟩ := sol.axiom_v'' x' hx'
        have h3 : ¬ (x' = x ∧ x' = y) := by
          contrapose! hxy
          rw [←hxy.1, ←hxy.2]
        have h4 : ¬ (x' = z ∧ x' = x) := by
          contrapose! hx
          rw [←hx.2, hx.1]
          exact gen_fresh_pow_not_in_dom_S' _ _ _ (Ne.symm (Nat.zero_ne_add_one 1))
        simp [h1, ←h2, h3, h4]
      rw [←hx'.2, hx'.1] at hx
      contrapose! hx
      exact gen_fresh_pow_not_in_dom_S' _ _ _ (Ne.symm (Nat.zero_ne_add_one 1))
    axiom_vi'' := by
      intro y' a hray'
      simp only [Finset.union_insert, Finset.mem_insert, Prod.mk.injEq, Finset.mem_union,
        Finset.mem_singleton] at hray'
      have hnot : ¬ (R' a y' = x ∧ y' = y) := by
          contrapose! hray
          obtain ⟨ h1, h2 ⟩ := hray
          rw [h2] at h1
          exact ⟨ a, h1.symm ⟩
      have hnot' : ¬ (R' a y' = z ∧ y' = x) := by
          by_contra h
          obtain ⟨ h1, h2 ⟩ := h
          rw [h2] at h1
          have : x = (e a)⁻¹ * (e d0)^2 := by
            simp [R', z] at h1
            calc
              _ = (e a)⁻¹ * (e a * x)  := by group
              _ = _ := by rw [h1]
          rw [this] at hx
          replace hx := (sol.dom_S'_involved {x,y,w} hx).1
          simp only [PartialSolution.sees, generators_subset_iff] at hx
          apply sol.fresh_not_in_gen {x,y,w} 0 $ hx d0 $ basis_elements_of_prod_gen d0 a
      simp only [hnot, hnot', or_false, false_or] at hray'
      obtain ⟨ h1, h2 ⟩ := sol.axiom_vi'' y' a hray'
      rw [←h2]
      simp [h1, hnot, hnot']
    axiom_vii'' := by
      intro x' y' hneq hxray hop
      simp only [Finset.union_insert, Finset.mem_insert, Prod.mk.injEq, Finset.mem_union,
        Finset.mem_singleton] at hop
      by_cases hop1 : x' = x ∧ y' = y
      . simp only [hop1.1, hop1.2, ↓reduceIte, Sum.inr.injEq, Finset.mem_union, Finset.mem_singleton,
        Prod.mk.injEq, Finset.union_insert, Finset.mem_insert, and_true, exists_eq_left', or_true, true_and]
        right
        simp only [hw, ↓reduceIte, hxy, and_false, and_self, z', and_true, hx]
      by_cases hop2 : x' = z ∧ y' = x
      . rw [hop2.1, hop2.2]
        use z'
        simp only [Prod.mk.injEq, hxy, and_false, ↓reduceIte, Finset.mem_union, Finset.mem_singleton,
        or_true, Finset.union_insert, Finset.mem_insert, true_or, and_self]
      have hop3 : (x', y') ∈ PartialSolution.Dom_op := by tauto
      have := sol.axiom_vii'' x' y' hneq hxray hop3
      obtain ⟨ z'', h1, h2 ⟩ := this
      refine ⟨ z'', ?_, ?_ ⟩
      . simp only [Prod.mk.injEq, hop1, ↓reduceIte, hop2, h1]
      rcases h2 with h2 | ⟨ h3, h3', h4, h5 ⟩
      . simp only [Finset.mem_union, h2, Finset.mem_singleton, Prod.mk.injEq, true_or,
        Finset.union_insert, Finset.mem_insert]
      right
      have h6 : ¬ (z'' = x ∧ x' = y) := by
        contrapose! hdef
        rwa [hdef.1, hdef.2] at h3
      have h7 : ¬ (z'' = z ∧ x' = x) := by
        by_contra h7
        rw [h7.1] at h3
        exact hz_invis (sol.dom_op_involved {x,y,w} h3).1
      simp only [Finset.union_insert, Finset.mem_insert, Prod.mk.injEq, h6, Finset.mem_union, h3, h3',
        Finset.mem_singleton, h7, or_false, or_true, hw, ↓reduceIte, true_and, h4, h5]
    axiom_P := by
      intro x'' y'' z'' hI
      simp only [Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq] at hI
      rcases hI with hI | ⟨ rfl, rfl, rfl ⟩
      . convert sol.axiom_P x'' y'' z'' hI using 2
        have h1 : ¬ (z'' = x ∧ x'' = y) := by
          contrapose! no_pending
          rw [no_pending.1, no_pending.2] at hI
          exact ⟨ y'', hI ⟩
        have h2 : ¬ (z'' = z ∧ x'' = x) := by
          by_contra h2
          rw [h2.1, h2.2] at hI
          exact (sol.axiom_P x y'' z hI).1 hx
        simp only [Finset.union_insert, Finset.mem_insert, Prod.mk.injEq, h1, Finset.mem_union,
          Finset.mem_singleton, h2, or_false, false_or]
      have hz : z ∉ sol.Dom_S' := by
        by_contra h3
        exact hz_invis $ (sol.dom_S'_involved {y'',y,w} h3).1

      have hz'_vis : sol.sees {y'',y,w} z' := by
        simp only [hw, ↓reduceIte, z']
        exact sol.sees_R'_inv (sol.reaches_S $ sol.reaches_involved $ (sol.dom_S'_involved _ hx).2) (sol.dom_L₀'_involved _ hw).2
      refine ⟨ hz, ?_, ?_, ?_, ?_, ?_ ⟩
      . by_contra h3
        simp only [Finset.union_insert, Finset.mem_insert, Prod.mk.injEq, Finset.mem_union,
          Finset.mem_singleton] at h3
        rcases h3 with ⟨ h3, h4 ⟩ | h3 | ⟨ h3, h4 ⟩
        . rw [h4] at hz
          exact hz hy
        . exact hz_invis (sol.dom_op_involved {y'',y,w} h3).2.1
        rw [h4] at hz
        exact hz hx
      . by_contra h
        contrapose! hz_invis
        rw [← h]
        exact hz'_vis
      . intro a
        have : ¬ sol.sees {y'',y,w} ( R' a z ) := by
          by_contra h
          dsimp [R',z, PartialSolution.sees] at h
          simp only [generators_subset_iff] at h
          apply sol.fresh_not_in_gen {y'',y,w} 0 $ h d0 $ basis_elements_of_prod_gen' d0 a
        contrapose! this
        rw [← this]
        exact hz'_vis
      . contrapose! hz_invis
        rw [←hz_invis]
        apply sol.extras_involved
        simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
      simp only [z, parent_of_e_sq]
      contrapose! hz_invis'
      rw [← hz_invis']
      apply sol.extras_involved
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
    axiom_P' := by
      intro x₁ y₁ y'₁ z₁ hy hy'
      simp only [Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq] at hy hy'
      have (y₁ : N) : (z, y₁, z₁) ∉ sol.I := by
        contrapose! hz_invis
        exact (sol.I_involved _ hz_invis).1

      rcases hy with hy | ⟨ hy₁, hy₂, hy₃ ⟩
      . rcases hy' with hy' | ⟨ hy'₁, hy'₂, hy'₃ ⟩
        . exact sol.axiom_P' x₁ y₁ y'₁ z₁ hy hy'
        replace this := this y₁
        contrapose! this
        rwa [hy'₁] at hy
      rcases hy' with hy' | ⟨ hy'₁, hy'₂, hy'₃ ⟩
      . replace this := this y'₁
        contrapose! this
        rwa [hy₁] at hy'
      rw [hy₂, hy'₂]
    axiom_L := sol.axiom_L
  }
  refine ⟨ sol', ?_, Finset.mem_union_right _ $ Finset.mem_insert_self (x, y) {(z, x)} ⟩
  refine ⟨ ?_, Finset.subset_union_left, by rfl, ?_, ?_, ?_ ⟩
  . simp only [Prod.mk.injEq, hw, ↓reduceIte, Finset.union_insert, subset_refl, sol']
  . intro x' hx'
    simp only [hw, ↓reduceIte, Prod.mk.injEq, sol', new_L₀']
  . intro (x',y') hxy'
    have h1 : ¬ (x' = x ∧ y' = y) := by
      contrapose! hdef
      rwa [hdef.1, hdef.2] at hxy'
    have h2 : ¬ (x' = z ∧ y' = x) := by
      by_contra h2
      rw [h2.1, h2.2] at hxy'
      exact hz_invis (sol.dom_op_involved {x,y,w} hxy').1
    simp only [Prod.mk.injEq, h1, ↓reduceIte, h2, sol']
  intros; rfl

end Eq1729
