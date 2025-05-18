import Mathlib.Tactic
import equational_theories.Equations.All
import equational_theories.Magma

namespace SimpleRewrites



@[equational_result]
theorem Equation816_implies_Equation795 (G : Type*) [Magma G] (h : Equation816 G) : Equation795 G := λ x y z w u => h x y z w x u
@[equational_result]
theorem Equation1628_implies_Equation1607 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1607 G := λ x y z w u => h x y z w x u
@[equational_result]
theorem Equation2440_implies_Equation2419 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2419 G := λ x y z w u => h x y z w x u
@[equational_result]
theorem Equation3455_implies_Equation3434 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3434 G := λ x y z w u => h x y z w x u
@[equational_result]
theorem Equation3658_implies_Equation3637 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3637 G := λ x y z w u => h x y z w x u
@[equational_result]
theorem Equation4064_implies_Equation4043 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4043 G := λ x y z w u => h x y z w x u
@[equational_result]
theorem Equation4582_implies_Equation4561 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4561 G := λ x y z w u => h x y z w x u
end SimpleRewrites
