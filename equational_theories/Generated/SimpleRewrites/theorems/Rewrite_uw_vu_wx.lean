import Mathlib.Tactic
import equational_theories.Equations.All
import equational_theories.Magma

namespace SimpleRewrites



@[equational_result]
theorem Equation1222_implies_Equation1162 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1162 G := λ x y z w u => h x y z x w u
@[equational_result]
theorem Equation1425_implies_Equation1365 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1365 G := λ x y z w u => h x y z x w u
@[equational_result]
theorem Equation1628_implies_Equation1568 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1568 G := λ x y z w u => h x y z x w u
@[equational_result]
theorem Equation2034_implies_Equation1974 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1974 G := λ x y z w u => h x y z x w u
@[equational_result]
theorem Equation2237_implies_Equation2177 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2177 G := λ x y z w u => h x y z x w u
@[equational_result]
theorem Equation2440_implies_Equation2380 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2380 G := λ x y z w u => h x y z x w u
@[equational_result]
theorem Equation2643_implies_Equation2583 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2583 G := λ x y z w u => h x y z x w u
@[equational_result]
theorem Equation3049_implies_Equation2989 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2989 G := λ x y z w u => h x y z x w u
@[equational_result]
theorem Equation3658_implies_Equation3598 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3598 G := λ x y z w u => h x y z x w u
@[equational_result]
theorem Equation3861_implies_Equation3801 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3801 G := λ x y z w u => h x y z x w u
@[equational_result]
theorem Equation4064_implies_Equation4004 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4004 G := λ x y z w u => h x y z x w u
end SimpleRewrites
