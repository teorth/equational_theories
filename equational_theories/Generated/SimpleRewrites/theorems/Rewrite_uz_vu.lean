import Mathlib.Tactic
import equational_theories.Equations.All
import equational_theories.Magma

namespace SimpleRewrites



@[equational_result]
theorem Equation613_implies_Equation602 (G : Type*) [Magma G] (h : Equation613 G) : Equation602 G := λ x y z w u => h x y z w z u
@[equational_result]
theorem Equation816_implies_Equation805 (G : Type*) [Magma G] (h : Equation816 G) : Equation805 G := λ x y z w u => h x y z w z u
@[equational_result]
theorem Equation1222_implies_Equation1211 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1211 G := λ x y z w u => h x y z w z u
@[equational_result]
theorem Equation1425_implies_Equation1414 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1414 G := λ x y z w u => h x y z w z u
@[equational_result]
theorem Equation1628_implies_Equation1617 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1617 G := λ x y z w u => h x y z w z u
@[equational_result]
theorem Equation2034_implies_Equation2023 (G : Type*) [Magma G] (h : Equation2034 G) : Equation2023 G := λ x y z w u => h x y z w z u
@[equational_result]
theorem Equation2237_implies_Equation2226 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2226 G := λ x y z w u => h x y z w z u
@[equational_result]
theorem Equation2643_implies_Equation2632 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2632 G := λ x y z w u => h x y z w z u
@[equational_result]
theorem Equation3049_implies_Equation3038 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3038 G := λ x y z w u => h x y z w z u
@[equational_result]
theorem Equation3861_implies_Equation3850 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3850 G := λ x y z w u => h x y z w z u
end SimpleRewrites
