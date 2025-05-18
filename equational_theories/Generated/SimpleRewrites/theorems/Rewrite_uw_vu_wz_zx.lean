import Mathlib.Tactic
import equational_theories.Equations.All
import equational_theories.Magma

namespace SimpleRewrites



@[equational_result]
theorem Equation1019_implies_Equation905 (G : Type*) [Magma G] (h : Equation1019 G) : Equation905 G := λ x y z w u => h x y x z w u
@[equational_result]
theorem Equation1425_implies_Equation1311 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1311 G := λ x y z w u => h x y x z w u
@[equational_result]
theorem Equation1831_implies_Equation1717 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1717 G := λ x y z w u => h x y x z w u
@[equational_result]
theorem Equation2643_implies_Equation2529 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2529 G := λ x y z w u => h x y x z w u
@[equational_result]
theorem Equation3049_implies_Equation2935 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2935 G := λ x y z w u => h x y x z w u
@[equational_result]
theorem Equation4379_implies_Equation4338 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4338 G := λ x y z w u => h x y x z w u
end SimpleRewrites
