import equational_theories.FreshGenerator
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.ManuallyProved.Equation1729.SmallMagma

namespace Eq1729

/-- `fill D` is the set of elements of the form (e 0)^n x with x in D and n an integer. -/

def fill (D: Finset N) : Set N := { y | ∃ (n : ℤ) (x : N), y = x * (e 0)^n ∧ x ∈ D }

@[simp]
lemma fill_empty : fill Finset.empty = ∅ := by
  ext y
  simp only [fill, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
  exact fun _ _ _ ↦ Finset.not_mem_empty _

lemma fill_mono {D₁ D₂ : Finset N} (h : D₁ ⊆ D₂) : fill D₁ ⊆ fill D₂ := by
  intro y hy
  rcases hy with ⟨n, x, hx, hD⟩
  exact ⟨n, x, hx, h hD⟩

class PartialSolution where
  L₀' : N → N
  op : N → N → M
  S' : N → SM
  I : Finset (N × N × N)
  Predom_L₀' : Finset N
  Dom_op : Finset (N × N)
  Dom_S' : Finset N
  axiom_i'' (x y : N) (h: x ∈ Predom_L₀') (h' : L₀' x = y) (n:ℤ) : L₀' (x * (e 0)^n) = y * (e 0)^n ∧ L₀' (y * (e 0)^n) = x * (e 0)^(n-1)
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
noncomputable def Set.choose {α: Type} {S: Set α} {P: α → Prop} (h: ∃ s ∈ S, P s) : S :=
  {
    val := Classical.choose h
    property := (Classical.choose_spec h).1
  }

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
    obtain ⟨ m, y, hx, hy ⟩ := h1.1
    change L₀' (L₀' x) = x * (e 0)⁻¹
    have := sol.1.axiom_i'' y (sol.1.L₀' y) hy rfl m
    rw [←h2.2, ←h1.2, hx, this.1, this.2, mul_assoc]
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


lemma enlarge_L₀' (sol : PartialSolution) (x:N)  : ∃ sol' : PartialSolution, sol ≤ sol' ∧ x ∈ fill sol'.Predom_L₀' := by sorry

lemma enlarge_S' (sol : PartialSolution) (x:N) : ∃ sol' : PartialSolution, sol ≤ sol' ∧ x ∈ sol'.Dom_S' := by sorry

lemma enlarge_op (sol : PartialSolution) (x y :N) : ∃ sol' : PartialSolution, sol ≤ sol' ∧ (x,y) ∈ sol'.Dom_op := by sorry


end Eq1729
