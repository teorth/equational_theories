import Mathlib.Tactic
import Mathlib.Data.Nat.Defs
import equational_theories.Equations.All
import equational_theories.Magma

namespace SimpleRewrites



@[equational_result]
theorem Equation1222_implies_Equation1145 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1145 G := λ x y z w u => h x y y z w u
@[equational_result]
theorem Equation1628_implies_Equation1551 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1551 G := λ x y z w u => h x y y z w u
@[equational_result]
theorem Equation2034_implies_Equation1957 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1957 G := λ x y z w u => h x y y z w u
@[equational_result]
theorem Equation2237_implies_Equation2160 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2160 G := λ x y z w u => h x y y z w u
@[equational_result]
theorem Equation2643_implies_Equation2566 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2566 G := λ x y z w u => h x y y z w u
@[equational_result]
theorem Equation3658_implies_Equation3581 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3581 G := λ x y z w u => h x y y z w u
@[equational_result]
theorem Equation3861_implies_Equation3784 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3784 G := λ x y z w u => h x y y z w u
@[equational_result]
theorem Equation4064_implies_Equation3987 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3987 G := λ x y z w u => h x y y z w u
@[equational_result]
theorem Equation4267_implies_Equation4190 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4190 G := λ x y z w u => h x y y z w u
end SimpleRewrites
