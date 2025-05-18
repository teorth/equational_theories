import Mathlib.Tactic
import equational_theories.Equations.All
import equational_theories.Magma

namespace SimpleRewrites



@[equational_result]
theorem Equation3455_implies_Equation3450 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3450 G := λ x y z w u => h x y z w u x
@[equational_result]
theorem Equation3658_implies_Equation3653 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3653 G := λ x y z w u => h x y z w u x
@[equational_result]
theorem Equation4064_implies_Equation4059 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4059 G := λ x y z w u => h x y z w u x
end SimpleRewrites
