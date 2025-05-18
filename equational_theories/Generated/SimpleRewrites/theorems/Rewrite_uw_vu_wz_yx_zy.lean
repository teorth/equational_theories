import Mathlib.Tactic
import equational_theories.Equations.All
import equational_theories.Magma

namespace SimpleRewrites



@[equational_result]
theorem Equation3455_implies_Equation3304 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3304 G := λ x y z w u => h x x y z w u
@[equational_result]
theorem Equation4694_implies_Equation4628 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4628 G := λ x y z w u => h x x y z w u
end SimpleRewrites
