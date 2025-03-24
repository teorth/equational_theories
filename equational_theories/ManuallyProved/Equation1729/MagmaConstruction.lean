import equational_theories.FreshGenerator
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.ManuallyProved.Equation1729.SmallMagma

namespace Eq1729

/-- `fill D` is the set of elements of the form (e 0)^n x with x in D and n an integer. -/

def fill (D: Finset N) : Set N := { y | ∃ (n : ℤ) (x : N), y = (e 0)^n * x ∧ x ∈ D }

@[simp]
lemma fill_empty : fill Finset.empty = ∅ := by
  ext y
  simp only [fill, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
  intros
  exact Finset.not_mem_empty _

class PartialSolution where
  L₀' : N → N
  op : N → N → M
  S' : N → SM
  I : Finset (N × N × N)
  Predom_L₀' : Finset N
  Dom_op : Finset (N × N)
  Dom_S' : Finset N
  axiom_i'' (x y : N) (h: x ∈ fill Predom_L₀') (h' : L₀' x = y) (n:ℤ) : L₀' ((e 0)^n * x) = (e 0)^n * y ∧ L₀' ((e 0)^n * y) = (e 0)^(n-1) * x
  axiom_S (x y : N) (h : x ∈ Dom_S') (h' : y ≤ x) : y ∈ Dom_S'
  axiom_iii'' (x y : N) (a : SM) (hx: x ∈ Dom_S') (hy: y ∈ Dom_S') (h: R' a x = y) : R' (S (a - S' x)) y ∈ fill Predom_L₀' ∧ (R' (S (S' x)) $ R'_inv (S' x) $ L₀' $ R' (S (a - S' x)) y ) ∈ fill Predom_L₀' ∧ (R'_inv (S' x) $ L₀' $ R' (S (S' x)) $ R'_inv (S' x) $ L₀' $ R' (S (a - S' x)) y ) = x
  axiom_iv'' (x : N) (h : x ∈ Dom_S') : R' (S (S' x)) x ∈ fill Predom_L₀' ∧ (R' (S (S' x)) $ R'_inv (S' x) $ L₀' $ R' (S (S' x)) x) ∈ fill Predom_L₀' ∧ (R'_inv (S' x) $ L₀' $ R' (S (S' x)) $ R'_inv (S' x) $ L₀' $ R' (S (S' x)) x) = x
  axiom_v'' (x : N) (h : (x,x) ∈ Dom_op) : x ∈ Dom_S' ∧ Sum.inl (S' x) = op x x
  axiom_vi'' (y : N) (a : SM) (h: (R' a y, y) ∈ Dom_op) : y ∈ Dom_S' ∧ Sum.inl ( a - S' y ) = op (R' a y) y
  axiom_vii'' (x y : N) (h : x ≠ y) (h' : ∀ a : SM, x ≠ R' a y) (hop: (x,y) ∈ Dom_op) : ∃ z : N, op x y = Sum.inr z ∧ ((x,y,z) ∈ I ∨ ((z,x) ∈ Dom_op ∧ (R' 0 $ R' (S' x) $ y) ∈ fill Predom_L₀' ∧ op z x = Sum.inr (R'_inv (S (S' x)) $ L₀' $ R' 0 $ R' (S' x) $ y)))
  axiom_P (x y z : N) (h: (x,y,z) ∈ I) : x ∉ Dom_S' ∧ (z,x) ∉ Dom_op ∧ z ≠ x ∧ (∀ a : SM, z ≠ R' a x)

/-- Not sure if this is the canonical way to proceed, but in order to impose a partial order on PartialSolution I had to first define the LE instance. -/
instance PartialSolution_LE : LE PartialSolution  := {
  le := by
    intro sol1 sol2
    exact sol1.Predom_L₀' ⊆ sol2.Predom_L₀' ∧ sol1.Dom_op ⊆ sol2.Dom_op ∧ sol1.Dom_S' ⊆ sol2.Dom_S' ∧ ∀ x, x ∈ fill sol1.Predom_L₀' → sol1.L₀' x = sol2.L₀' x ∧ ∀ z ∈ sol1.Dom_op, sol1.op z.1 z.2 = sol2.op z.1 z.2 ∧ ∀ x ∈ sol1.Dom_S', sol1.S' x = sol2.S' x
}

/-- Impose a preorder on solutions using the notion of an extension. -/
instance PartialSolution_order : Preorder PartialSolution  := {
  le := PartialSolution_LE.le
  lt := by
    intro sol1 sol2
    exact sol1 ≤ sol2 ∧ sol1 ≠ sol2
  le_refl := sorry
  le_trans := sorry
  lt_iff_le_not_le := sorry
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
    intro _ _
    simp only [fill_empty, Set.mem_empty_iff_false, IsEmpty.forall_iff]
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

lemma use_chain (sol : ℕ → PartialSolution) (hsol: Monotone sol) (htotal_L₀' : ∀ x : N, ∃ n : ℕ, x ∈ fill (sol n).Predom_L₀') (htotal_S' : ∀ x : N, ∃ n : ℕ, x ∈ (sol n).Dom_S') (htotal_op : ∀ (x y : N), ∃ n : ℕ, (x,y) ∈ (sol n).Dom_op) : ∃ (G: Type) (_: Magma G), Equation1729 G ∧ ¬ Equation817 G := by sorry

lemma enlarge_L₀' (sol : PartialSolution) (x:N)  : ∃ sol' : PartialSolution, sol' ≥ sol ∧ x ∈ fill sol'.Predom_L₀' := by sorry

lemma enlarge_S' (sol : PartialSolution) (x:N) : ∃ sol' : PartialSolution, sol' ≥ sol ∧ x ∈ sol'.Dom_S' := by sorry

lemma enlarge_op (sol : PartialSolution) (x y :N) : ∃ sol' : PartialSolution, sol' ≥ sol ∧ (x,y) ∈ sol'.Dom_op := by sorry


end Eq1729
