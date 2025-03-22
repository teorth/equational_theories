import equational_theories.FreshGenerator
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.ManuallyProved.Equation1729.SmallMagma

namespace Eq1729

/-- `fill D` is the set of elements of the form (e 0)^n x with x in D and n an integer. -/

def fill (D: Finset N) : Set N := { y | ∃ (n : ℤ) (x : N), y = (e 0)^n * x ∧ x ∈ D }

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

/-- Impose a partial order on solutions using the notion of an extension. -/
instance PartialSolution_order : PartialOrder PartialSolution  := by sorry

/-- The trivial partial solution. -/
def TrivialPartialSolution : PartialSolution := by
  sorry

lemma use_chain (sol : ℕ → PartialSolution) (hsol: Monotone sol) (htotal_L₀' : ∀ x : N, ∃ n : ℕ, x ∈ fill (sol n).Predom_L₀') (htotal_S' : ∀ x : N, ∃ n : ℕ, x ∈ (sol n).Dom_S') (htotal_op : ∀ (x y : N), ∃ n : ℕ, (x,y) ∈ (sol n).Dom_op) : ∃ (G: Type) (_: Magma G), Equation1729 G ∧ ¬ Equation817 G := by sorry

lemma enlarge_L₀' (sol : PartialSolution) (x:N)  : ∃ sol' : PartialSolution, sol' ≥ sol ∧ x ∈ fill sol'.Predom_L₀' := by sorry

lemma enlarge_S' (sol : PartialSolution) (x:N) : ∃ sol' : PartialSolution, sol' ≥ sol ∧ x ∈ sol'.Dom_S' := by sorry

lemma enlarge_op (sol : PartialSolution) (x y :N) : ∃ sol' : PartialSolution, sol' ≥ sol ∧ (x,y) ∈ sol'.Dom_op := by sorry


end Eq1729
