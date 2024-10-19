import equational_theories.Equations.All
import equational_theories.FreeMagma

theorem ExpressionEqualsAnything_implies_Equation2 (G: Type _) [Magma G] :
    (∃ n : Nat, ∃ expr : FreeMagma (Fin n), ∀ x : G, ∀ sub : Fin n → G, x = expr.evalInMagma sub) → Equation2 G :=
  fun  ⟨_, _, univ⟩ x y ↦ (univ x fun _ ↦ x).trans (univ y fun _ ↦ x).symm

theorem Equation37_implies_Equation2 (G : Type _) [Magma G] :
    (∀ x y z w : G, x = (y ◇ z) ◇ w) → Equation2 G :=
  fun univ ↦ ExpressionEqualsAnything_implies_Equation2 G ⟨
    3,
    (Lf 0 ⋆ Lf 1) ⋆ Lf 2, -- The syntactic representation of (y ◇ z) ◇ w
    fun k sub ↦ univ k (sub 0) (sub 1) (sub 2)
  ⟩

theorem Equation514_implies_Equation2 (G : Type _) [Magma G] :
    (∀ x y : G, x = y ◇ (y ◇ (y ◇ y))) → Equation2 G :=
  fun univ ↦ ExpressionEqualsAnything_implies_Equation2 G ⟨
    1,
    Lf 0 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0)), -- The syntactic representation of y ◇ (y ◇ (y ◇ y)))
    fun k sub ↦ univ k (sub 0)
  ⟩
