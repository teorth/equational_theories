import Mathlib.Tactic
import Mathlib.Data.Nat.Defs
import equational_theories.Equations.All
import equational_theories.Magma

namespace SimpleRewrites



@[equational_result]
theorem Equation816_implies_Equation800 (G : Type*) [Magma G] (h : Equation816 G) : Equation800 G := λ x y z w u => h x y z w y u
@[equational_result]
theorem Equation1019_implies_Equation1003 (G : Type*) [Magma G] (h : Equation1019 G) : Equation1003 G := λ x y z w u => h x y z w y u
@[equational_result]
theorem Equation1222_implies_Equation1206 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1206 G := λ x y z w u => h x y z w y u
@[equational_result]
theorem Equation1628_implies_Equation1612 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1612 G := λ x y z w u => h x y z w y u
@[equational_result]
theorem Equation2034_implies_Equation2018 (G : Type*) [Magma G] (h : Equation2034 G) : Equation2018 G := λ x y z w u => h x y z w y u
@[equational_result]
theorem Equation2237_implies_Equation2221 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2221 G := λ x y z w u => h x y z w y u
@[equational_result]
theorem Equation2643_implies_Equation2627 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2627 G := λ x y z w u => h x y z w y u
@[equational_result]
theorem Equation3049_implies_Equation3033 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3033 G := λ x y z w u => h x y z w y u
@[equational_result]
theorem Equation3658_implies_Equation3642 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3642 G := λ x y z w u => h x y z w y u
@[equational_result]
theorem Equation4064_implies_Equation4048 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4048 G := λ x y z w u => h x y z w y u
end SimpleRewrites
