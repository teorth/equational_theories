import Mathlib.Data.Set.Finite.Basic

import equational_theories.EquationalResult
import equational_theories.Equations.All

namespace Eq1441

/- Proofs can be found at https://teorth.github.io/equational_theories/blueprint/infinite-model-chapter.html#1441-4067-1443-3055 -/

@[equational_result]
theorem Finite.Equation1441_implies_Equation4067 (G : Type) [Magma G] [Finite G] (h : Equation1441 G) :
    Equation4067 G := by
  intro x y
  let C (x : G) := x ◇ (x ◇ x)
  let S (x : G) := x ◇ x
  have inv : Function.RightInverse (C ·) (S ·) := by
    intro x
    symm
    apply h
  have inv2 := Function.leftInverse_of_surjective_of_rightInverse
    (Finite.surjective_of_injective inv.injective) inv
  have t : S x = ((S x) ◇ y) ◇ (C (S x)) := by apply h (S x)
  rw [show C (S x) = x by apply inv2] at t
  exact t

@[equational_result]
theorem Finite.Equation1443_implies_Equation3055 (G : Type) [Magma G] [Finite G] (h : Equation1443 G) :
    Equation3055 G := by
  intro x y
  let C (x : G) := x ◇ (x ◇ x)
  let S (x : G) := x ◇ x
  have inv : Function.RightInverse (C ·) (S ·) := by
    intro x
    symm
    apply h
  have inv2 := Function.leftInverse_of_surjective_of_rightInverse
    (Finite.surjective_of_injective inv.injective) inv
  have eq1441 : Equation1441 G := by intro x y; apply h x y x
  have eq4067 : Equation4067 G := by apply Finite.Equation1441_implies_Equation4067 G eq1441
  rw [← eq4067]
  have : x = C (S x) := by exact (inv2 x).symm
  nth_rewrite 4 [this]
  nth_rewrite 1 [this]
  have (x z : G) : x = S (x ◇ (x ◇ z)) := by exact h x (x ◇ z) z
  have (x z : G) : C x = x ◇ (x ◇ z) := by
    apply inv2.injective
    simp only
    rw [← this, ← this]
  have (x : G) : C x = x ◇ (C x) := by apply this x (S x)
  apply this

/- Proofs can be found at https://teorth.github.io/equational_theories/blueprint/infinite-model-chapter.html#1681-3877-1701-1035 -/

@[equational_result]
theorem Finite.Equation1681_implies_Equation3877 (G : Type) [Magma G] [Finite G] (h : Equation1681 G) :
    Equation3877 G := by
  intro x y
  let C (x : G) := (x ◇ x) ◇ x
  let S (x : G) := x ◇ x
  have inv : Function.RightInverse (C ·) (S ·) := by
    intro x
    symm
    apply h
  have inv2 := Function.leftInverse_of_surjective_of_rightInverse
    (Finite.surjective_of_injective inv.injective) inv
  have t : S x = (y ◇ (S x)) ◇ (C (S x)) := by exact h (S x) y
  rw [show C (S x) = x by apply inv2] at t
  exact t

@[equational_result]
theorem Finite.Equation1701_implies_Equation1035 (G : Type) [Magma G] [Finite G] (h : Equation1701 G) :
    Equation1035 G := by
  intro x y
  let C (x : G) := (x ◇ x) ◇ x
  let S (x : G) := x ◇ x
  have inv : Function.RightInverse (C ·) (S ·) := by
    intro x
    symm
    apply h
  have inv2 := Function.leftInverse_of_surjective_of_rightInverse
    (Finite.surjective_of_injective inv.injective) inv
  have eq1681 : Equation1681 G := by intro x y; apply h x y x
  have eq3877 : Equation3877 G := by apply Finite.Equation1681_implies_Equation3877 G eq1681
  rw [← eq3877]
  have : x = C (S x) := by exact (inv2 x).symm
  nth_rewrite 2 [this]
  nth_rewrite 1 [this]
  have (x z : G) : x = S ((z ◇ x) ◇ x) := by exact h x (z ◇ x) z
  have (x z : G) : C x = (z ◇ x) ◇ x := by
    apply inv2.injective
    simp only
    rw [← this, ← this]
  have (x : G) : C x = (C x) ◇ x := by apply this x (S x)
  apply this

end Eq1441
