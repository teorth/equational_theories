import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation3051_implies_Equation3082 (G : Type*) [Magma G] (h : Equation3051 G) : Equation3082 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = ((X0 ◇ ((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq13 (X0 X1 : G) : (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)))) ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1.1 in 11
  have eq17 (X0 X1 : G) : ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ X1) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq11 eq18 -- forward demodulation 18,11
  have eq20 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq32 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq20 eq20 -- superposition 20,20, 20 into 20, unify on (0).2 in 20 and (0).2 in 20
  have eq72 (X0 : G) : sK0 ≠ ((((sK0 ◇ X0) ◇ sK1) ◇ sK2) ◇ sK1) := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2.1.1.1 in 10
  have eq164 : sK0 ≠ ((((sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) ◇ sK2) ◇ sK1) := superpose eq17 eq72 -- superposition 72,17, 17 into 72, unify on (0).2 in 17 and (0).2.1.1 in 72
  have eq171 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK1) := superpose eq11 eq164 -- forward demodulation 164,11
  subsumption eq171 eq9


@[equational_result]
theorem Equation3051_implies_Equation3537 (G : Type*) [Magma G] (h : Equation3051 G) : Equation3537 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq13 (X0 X1 : G) : (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)))) ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1.1 in 11
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq11 eq18 -- forward demodulation 18,11
  have eq20 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq32 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq20 eq20 -- superposition 20,20, 20 into 20, unify on (0).2 in 20 and (0).2 in 20
  have eq72 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK2) ◇ X0)) := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2.2 in 10
  subsumption eq72 eq32


@[equational_result]
theorem Equation3051_implies_Equation3261 (G : Type*) [Magma G] (h : Equation3051 G) : Equation3261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq13 (X0 X1 : G) : (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)))) ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1.1 in 11
  have eq18 (X0 X1 : G) : (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = (X0 ◇ X1) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq19 (X0 X1 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = (X0 ◇ X1) := superpose eq11 eq18 -- forward demodulation 18,11
  have eq20 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = (X0 ◇ X1) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq32 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq20 eq20 -- superposition 20,20, 20 into 20, unify on (0).2 in 20 and (0).1 in 20
  have eq72 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2 in 10
  subsumption eq72 eq32


@[equational_result]
theorem Equation3051_implies_Equation4318 (G : Type*) [Magma G] (h : Equation3051 G) : Equation4318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq13 (X0 X1 : G) : (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)))) ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1.1 in 11
  have eq18 (X0 X1 : G) : (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = (X0 ◇ X1) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq19 (X0 X1 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = (X0 ◇ X1) := superpose eq11 eq18 -- forward demodulation 18,11
  have eq20 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = (X0 ◇ X1) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq32 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq20 eq20 -- superposition 20,20, 20 into 20, unify on (0).2 in 20 and (0).1 in 20
  have eq72 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ X0) := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2 in 10
  subsumption eq72 eq32


@[equational_result]
theorem Equation2702_implies_Equation2243 (G : Type*) [Magma G] (h : Equation2702 G) : Equation2243 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X1 X3 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2702_implies_Equation2249 (G : Type*) [Magma G] (h : Equation2702 G) : Equation2249 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X1 X3 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation3933_implies_Equation4474 (G : Type*) [Magma G] (h : Equation3933 G) : Equation4474 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X5 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X5) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2 in 14
  have eq29 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).1 in 15
  subsumption eq29 rfl


@[equational_result]
theorem Equation3933_implies_Equation379 (G : Type*) [Magma G] (h : Equation3933 G) : Equation379 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X5 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X5) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3933_implies_Equation3727 (G : Type*) [Magma G] (h : Equation3933 G) : Equation3727 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X5 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X5) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3933_implies_Equation4396 (G : Type*) [Magma G] (h : Equation3933 G) : Equation4396 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X5 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X5) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2 in 14
  have eq29 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).1 in 15
  subsumption eq29 rfl


@[equational_result]
theorem Equation3933_implies_Equation4512 (G : Type*) [Magma G] (h : Equation3933 G) : Equation4512 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X5 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X5) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2 in 14
  have eq29 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).1 in 15
  subsumption eq29 rfl


@[equational_result]
theorem Equation3933_implies_Equation3724 (G : Type*) [Magma G] (h : Equation3933 G) : Equation3724 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X5 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X5) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3933_implies_Equation4397 (G : Type*) [Magma G] (h : Equation3933 G) : Equation4397 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X5 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X5) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2 in 14
  have eq29 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).1 in 15
  subsumption eq29 rfl


@[equational_result]
theorem Equation3933_implies_Equation4437 (G : Type*) [Magma G] (h : Equation3933 G) : Equation4437 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X5 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X5) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2 in 14
  have eq29 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).1 in 15
  subsumption eq29 rfl


@[equational_result]
theorem Equation3933_implies_Equation4511 (G : Type*) [Magma G] (h : Equation3933 G) : Equation4511 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X5 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X5) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2 in 14
  have eq27 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).1 in 15
  subsumption eq27 rfl


@[equational_result]
theorem Equation3933_implies_Equation4513 (G : Type*) [Magma G] (h : Equation3933 G) : Equation4513 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK1) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X5 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X5) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2 in 14
  have eq29 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).1 in 15
  subsumption eq29 rfl


@[equational_result]
theorem Equation1009_implies_Equation1461 (G : Type*) [Magma G] (h : Equation1009 G) : Equation1461 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq13 (X2 X3 X4 : G) : (X2 ◇ X3) = (X4 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X1 X2 X3 X4 : G) : (X4 ◇ (X3 ◇ (X1 ◇ X2))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq26 (X0 : G) : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ (X0 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.2 in 10
  subsumption eq26 eq24


@[equational_result]
theorem Equation1009_implies_Equation1441 (G : Type*) [Magma G] (h : Equation1009 G) : Equation1441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq13 (X2 X3 X4 : G) : (X2 ◇ X3) = (X4 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 (X0 : G) : sK0 ≠ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq24 (X1 X2 X3 X4 : G) : (X4 ◇ (X3 ◇ (X1 ◇ X2))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq63 (X0 X1 : G) : sK0 ≠ (X1 ◇ (sK0 ◇ (X0 ◇ sK0))) := superpose eq13 eq23 -- superposition 23,13, 13 into 23, unify on (0).2 in 13 and (0).2.2.2 in 23
  subsumption eq63 eq24


@[equational_result]
theorem Equation1009_implies_Equation47 (G : Type*) [Magma G] (h : Equation1009 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X1 X2 X3 X4 X5 : G) : (X4 ◇ (X3 ◇ (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X5))) = X5 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq12 (X2 X3 X4 : G) : (X2 ◇ X3) = (X4 ◇ X3) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq19 (X0 : G) : sK0 ≠ (sK0 ◇ (sK0 ◇ (X0 ◇ sK0))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2.2 in 9
  have eq64 : sK0 ≠ sK0 := superpose eq10 eq19 -- superposition 19,10, 10 into 19, unify on (0).2 in 10 and (0).2 in 19
  subsumption eq64 rfl


@[equational_result]
theorem Equation1009_implies_Equation4104 (G : Type*) [Magma G] (h : Equation1009 G) : Equation4104 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X2 X3 X4 : G) : (X2 ◇ X3) = (X4 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 : G) : (sK0 ◇ sK0) ≠ (((X0 ◇ sK2) ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation1009_implies_Equation4121 (G : Type*) [Magma G] (h : Equation1009 G) : Equation4121 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X2 X3 X4 : G) : (X2 ◇ X3) = (X4 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ (((X0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation1009_implies_Equation4080 (G : Type*) [Magma G] (h : Equation1009 G) : Equation4080 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X2 X3 X4 : G) : (X2 ◇ X3) = (X4 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 : G) : (sK0 ◇ sK0) ≠ (((X0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation1009_implies_Equation4327 (G : Type*) [Magma G] (h : Equation1009 G) : Equation4327 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X3)) = (X4 ◇ ((X5 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X2 X3 X4 : G) : (X2 ◇ X3) = (X4 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 (X1 X2 X3 X4 : G) : (X4 ◇ (X3 ◇ (X1 ◇ X2))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq24 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (X0 ◇ sK0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  have eq61 (X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ X3)) = (X4 ◇ (X5 ◇ X3)) := superpose eq23 eq23 -- superposition 23,23, 23 into 23, unify on (0).2 in 23 and (0).1.2.2 in 23
  have eq170 (X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((X2 ◇ X3) ◇ (X3 ◇ sK0)) := superpose eq12 eq24 -- superposition 24,12, 12 into 24, unify on (0).2 in 12 and (0).2 in 24
  subsumption eq170 eq61


@[equational_result]
theorem Equation3479_implies_Equation3457 (G : Type*) [Magma G] (h : Equation3479 G) : Equation3457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X2) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X2)) = (X3 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X3 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq17 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq26 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq17 eq17 -- superposition 17,17, 17 into 17, unify on (0).2 in 17 and (0).2 in 17
  have eq96 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ ((X0 ◇ X0) ◇ sK1)) := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).1 in 10
  have eq600 (X0 : G) : (((sK1 ◇ X0) ◇ X0) ◇ ((sK1 ◇ X0) ◇ X0)) ≠ (((sK1 ◇ X0) ◇ X0) ◇ ((sK1 ◇ X0) ◇ X0)) := superpose eq13 eq96 -- superposition 96,13, 13 into 96, unify on (0).2 in 13 and (0).2 in 96
  subsumption eq600 rfl


@[equational_result]
theorem Equation3479_implies_Equation3461 (G : Type*) [Magma G] (h : Equation3479 G) : Equation3461 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X2) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X3 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq17 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq18 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq18 eq18 -- superposition 18,18, 18 into 18, unify on (0).2 in 18 and (0).2 in 18
  have eq54 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq17 -- superposition 17,27, 27 into 17, unify on (0).2 in 27 and (0).2 in 17
  subsumption eq54 eq27


@[equational_result]
theorem Equation3479_implies_Equation4341 (G : Type*) [Magma G] (h : Equation3479 G) : Equation4341 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X2) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X3 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq17 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq35 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq35 eq17


@[equational_result]
theorem Equation3479_implies_Equation3506 (G : Type*) [Magma G] (h : Equation3479 G) : Equation3506 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X2) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ sK3)) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X3 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq17 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq18 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq18 eq18 -- superposition 18,18, 18 into 18, unify on (0).2 in 18 and (0).2 in 18
  have eq54 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq17 -- superposition 17,27, 27 into 17, unify on (0).2 in 27 and (0).2 in 17
  subsumption eq54 eq27


@[equational_result]
theorem Equation3479_implies_Equation40 (G : Type*) [Magma G] (h : Equation3479 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X2) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X3 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq17 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq26 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq17 eq17 -- superposition 17,17, 17 into 17, unify on (0).2 in 17 and (0).2 in 17
  have eq96 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq96 eq26


@[equational_result]
theorem Equation3479_implies_Equation3489 (G : Type*) [Magma G] (h : Equation3479 G) : Equation3489 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X2) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X3 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq17 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq18 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq18 eq18 -- superposition 18,18, 18 into 18, unify on (0).2 in 18 and (0).2 in 18
  have eq54 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq17 -- superposition 17,27, 27 into 17, unify on (0).2 in 27 and (0).2 in 17
  subsumption eq54 eq27


@[equational_result]
theorem Equation3479_implies_Equation3256 (G : Type*) [Magma G] (h : Equation3479 G) : Equation3256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X2) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X3 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq17 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq35 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2.2 in 10
  subsumption eq35 eq17


@[equational_result]
theorem Equation3479_implies_Equation3665 (G : Type*) [Magma G] (h : Equation3479 G) : Equation3665 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X2) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X3 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq17 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq29 (X0 X1 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ (X1 ◇ X1)) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq29 eq17


@[equational_result]
theorem Equation598_implies_Equation487 (G : Type*) [Magma G] (h : Equation598 G) : Equation487 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X4 ◇ (X2 ◇ X1)))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2.2 in 9
  have eq24 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  subsumption eq24 eq20


@[equational_result]
theorem Equation1449_implies_Equation158 (G : Type*) [Magma G] (h : Equation1449 G) : Equation158 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3280_implies_Equation3256 (G : Type*) [Magma G] (h : Equation3280 G) : Equation3256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation3280_implies_Equation3257 (G : Type*) [Magma G] (h : Equation3280 G) : Equation3257 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.2 in 9
  have eq37 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq27 -- superposition 27,9, 9 into 27, unify on (0).2 in 9 and (0).2 in 27
  have eq105 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq37 eq16 -- superposition 16,37, 37 into 16, unify on (0).2 in 37 and (0).2 in 16
  subsumption eq105 eq37


@[equational_result]
theorem Equation3280_implies_Equation3255 (G : Type*) [Magma G] (h : Equation3280 G) : Equation3255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.2 in 9
  have eq37 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq27 -- superposition 27,9, 9 into 27, unify on (0).2 in 9 and (0).2 in 27
  have eq105 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq37 eq16 -- superposition 16,37, 37 into 16, unify on (0).2 in 37 and (0).2 in 16
  subsumption eq105 eq37


@[equational_result]
theorem Equation3280_implies_Equation3283 (G : Type*) [Magma G] (h : Equation3280 G) : Equation3283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.2 in 9
  have eq37 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq27 -- superposition 27,9, 9 into 27, unify on (0).2 in 9 and (0).2 in 27
  have eq105 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq37 eq16 -- superposition 16,37, 37 into 16, unify on (0).2 in 37 and (0).2 in 16
  subsumption eq105 eq37


@[equational_result]
theorem Equation3280_implies_Equation3664 (G : Type*) [Magma G] (h : Equation3280 G) : Equation3664 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X3 ◇ (X1 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq42 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq63 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ X2) := superpose eq14 eq42 -- superposition 42,14, 14 into 42, unify on (0).2 in 14 and (0).1 in 42
  have eq70 (X0 : G) : (X0 ◇ X0) ≠ ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := superpose eq42 eq10 -- superposition 10,42, 42 into 10, unify on (0).2 in 42 and (0).1 in 10
  subsumption eq70 eq63


@[equational_result]
theorem Equation3280_implies_Equation4341 (G : Type*) [Magma G] (h : Equation3280 G) : Equation4341 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation3280_implies_Equation40 (G : Type*) [Magma G] (h : Equation3280 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X3 ◇ (X1 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq42 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq70 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq42 eq10 -- superposition 10,42, 42 into 10, unify on (0).2 in 42 and (0).2 in 10
  subsumption eq70 eq42


@[equational_result]
theorem Equation3280_implies_Equation307 (G : Type*) [Magma G] (h : Equation3280 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.2 in 8
  have eq25 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2 in 9
  subsumption eq25 rfl


@[equational_result]
theorem Equation3280_implies_Equation3284 (G : Type*) [Magma G] (h : Equation3280 G) : Equation3284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.2 in 9
  have eq37 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq27 -- superposition 27,9, 9 into 27, unify on (0).2 in 9 and (0).2 in 27
  have eq105 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq37 eq16 -- superposition 16,37, 37 into 16, unify on (0).2 in 37 and (0).2 in 16
  subsumption eq105 eq37


@[equational_result]
theorem Equation3280_implies_Equation3285 (G : Type*) [Magma G] (h : Equation3280 G) : Equation3285 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.2 in 9
  have eq37 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq27 -- superposition 27,9, 9 into 27, unify on (0).2 in 9 and (0).2 in 27
  have eq105 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq37 eq16 -- superposition 16,37, 37 into 16, unify on (0).2 in 37 and (0).2 in 16
  subsumption eq105 eq37


@[equational_result]
theorem Equation3280_implies_Equation3287 (G : Type*) [Magma G] (h : Equation3280 G) : Equation3287 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.2 in 9
  have eq37 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq27 -- superposition 27,9, 9 into 27, unify on (0).2 in 9 and (0).2 in 27
  have eq105 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq37 eq16 -- superposition 16,37, 37 into 16, unify on (0).2 in 37 and (0).2 in 16
  subsumption eq105 eq37


@[equational_result]
theorem Equation1014_implies_Equation4023 (G : Type*) [Magma G] (h : Equation1014 G) : Equation4023 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq13 (X4 X5 X6 : G) : (X4 ◇ X5) = (X6 ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ ((sK2 ◇ (X0 ◇ sK0)) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.2 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation1014_implies_Equation3989 (G : Type*) [Magma G] (h : Equation1014 G) : Equation3989 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq13 (X4 X5 X6 : G) : (X4 ◇ X5) = (X6 ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq23 eq13


@[equational_result]
theorem Equation1014_implies_Equation4096 (G : Type*) [Magma G] (h : Equation1014 G) : Equation4096 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq13 (X4 X5 X6 : G) : (X4 ◇ X5) = (X6 ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 : G) : (sK0 ◇ sK0) ≠ (((X0 ◇ sK1) ◇ sK2) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation1014_implies_Equation649 (G : Type*) [Magma G] (h : Equation1014 G) : Equation649 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X4 X5 X6 X7 : G) : (X5 ◇ (X4 ◇ (X6 ◇ X7))) = X7 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X4 X5 X6 : G) : (X4 ◇ X5) = (X6 ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 : G) : sK0 ≠ (sK0 ◇ (sK1 ◇ ((X0 ◇ sK0) ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.2.1 in 10
  subsumption eq20 eq11


@[equational_result]
theorem Equation1014_implies_Equation4360 (G : Type*) [Magma G] (h : Equation1014 G) : Equation4360 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ sK2)) := mod_symm nh
  have eq11 (X4 X5 X6 X7 : G) : (X5 ◇ (X4 ◇ (X6 ◇ X7))) = X7 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X4 X5 X6 : G) : (X4 ◇ X5) = (X6 ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK3 ◇ sK2)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq33 (X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ X3)) = (X4 ◇ (X5 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq47 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK2)) ≠ (X1 ◇ (sK3 ◇ sK2)) := superpose eq13 eq24 -- superposition 24,13, 13 into 24, unify on (0).2 in 13 and (0).1.2 in 24
  subsumption eq47 eq33


@[equational_result]
theorem Equation1014_implies_Equation679 (G : Type*) [Magma G] (h : Equation1014 G) : Equation679 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq11 (X4 X5 X6 X7 : G) : (X5 ◇ (X4 ◇ (X6 ◇ X7))) = X7 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X4 X5 X6 : G) : (X4 ◇ X5) = (X6 ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ (X0 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.2 in 10
  subsumption eq23 eq11


@[equational_result]
theorem Equation1032_implies_Equation414 (G : Type*) [Magma G] (h : Equation1032 G) : Equation414 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ ((X3 ◇ X0) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1))) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq17 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq18 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq54 : sK0 ≠ sK0 := superpose eq15 eq18 -- superposition 18,15, 15 into 18, unify on (0).2 in 15 and (0).2 in 18
  subsumption eq54 rfl


@[equational_result]
theorem Equation1032_implies_Equation102 (G : Type*) [Magma G] (h : Equation1032 G) : Equation102 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ ((X3 ◇ X0) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1032_implies_Equation3915 (G : Type*) [Magma G] (h : Equation1032 G) : Equation3915 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ ((X3 ◇ X0) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1))) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq17 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq18 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq19 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq18 -- forward demodulation 18,17
  subsumption eq19 rfl


@[equational_result]
theorem Equation1032_implies_Equation4380 (G : Type*) [Magma G] (h : Equation1032 G) : Equation4380 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X3 : G) : (X3 ◇ ((X3 ◇ X0) ◇ X0)) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.2 in 8
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq16 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq12 -- forward demodulation 12,8
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq16 eq9 -- backward demodulation 9,16
  subsumption eq17 rfl


@[equational_result]
theorem Equation1032_implies_Equation413 (G : Type*) [Magma G] (h : Equation1032 G) : Equation413 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq29 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation1032_implies_Equation23 (G : Type*) [Magma G] (h : Equation1032 G) : Equation23 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X3 : G) : (X3 ◇ ((X3 ◇ X0) ◇ X0)) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.2 in 8
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq16 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq12 -- forward demodulation 12,8
  have eq17 : sK0 ≠ (sK0 ◇ sK0) := superpose eq16 eq9 -- backward demodulation 9,16
  subsumption eq17 eq16


@[equational_result]
theorem Equation1032_implies_Equation412 (G : Type*) [Magma G] (h : Equation1032 G) : Equation412 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ ((X3 ◇ X0) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1))) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq17 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq19 : sK0 ≠ (sK0 ◇ sK0) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq19 eq17


@[equational_result]
theorem Equation1032_implies_Equation415 (G : Type*) [Magma G] (h : Equation1032 G) : Equation415 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq29 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation3634_implies_Equation3343 (G : Type*) [Magma G] (h : Equation3634 G) : Equation3343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ ((X3 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X4)) = (X5 ◇ (X3 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq14 (X3 X4 X5 : G) : (X3 ◇ X4) = (X5 ◇ (X3 ◇ X4)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq15 eq14


@[equational_result]
theorem Equation3634_implies_Equation3837 (G : Type*) [Magma G] (h : Equation3634 G) : Equation3837 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ ((X3 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK3) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X4)) = (X5 ◇ (X3 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq14 (X3 X4 X5 : G) : (X3 ◇ X4) = (X5 ◇ (X3 ◇ X4)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq20 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation3634_implies_Equation4416 (G : Type*) [Magma G] (h : Equation3634 G) : Equation4416 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ ((X3 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X4)) = (X5 ◇ (X3 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq14 (X3 X4 X5 : G) : (X3 ◇ X4) = (X5 ◇ (X3 ◇ X4)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK0) ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X2 ◇ X3) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2 in 14
  have eq27 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).2 in 15
  subsumption eq27 rfl


@[equational_result]
theorem Equation3634_implies_Equation4564 (G : Type*) [Magma G] (h : Equation3634 G) : Equation4564 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ ((X3 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X4)) = (X5 ◇ (X3 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq14 (X3 X4 X5 : G) : (X3 ◇ X4) = (X5 ◇ (X3 ◇ X4)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK1 ◇ sK2) ≠ ((sK3 ◇ sK1) ◇ sK2) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X2 ◇ X3) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2 in 14
  have eq27 : (sK1 ◇ sK2) ≠ (sK1 ◇ sK2) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).2 in 15
  subsumption eq27 rfl


@[equational_result]
theorem Equation3634_implies_Equation4512 (G : Type*) [Magma G] (h : Equation3634 G) : Equation4512 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ ((X3 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X4)) = (X5 ◇ (X3 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq14 (X3 X4 X5 : G) : (X3 ◇ X4) = (X5 ◇ (X3 ◇ X4)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK1 ◇ sK2) ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X2 ◇ X3) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2 in 14
  have eq27 : (sK1 ◇ sK2) ≠ (sK1 ◇ sK2) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).2 in 15
  subsumption eq27 rfl


@[equational_result]
theorem Equation947_implies_Equation713 (G : Type*) [Magma G] (h : Equation947 G) : Equation713 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X3 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq20 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq17 eq9 -- backward demodulation 9,17
  have eq82 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq20 eq17 -- superposition 17,20, 20 into 17, unify on (0).2 in 20 and (0).1.2 in 17
  have eq93 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).1.2 in 20
  have eq117 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq17 eq82 -- forward demodulation 82,17
  have eq118 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := superpose eq20 eq117 -- forward demodulation 117,20
  have eq154 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq93 eq17 -- superposition 17,93, 93 into 17, unify on (0).2 in 93 and (0).1.2 in 17
  have eq163 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq17 eq154 -- forward demodulation 154,17
  have eq164 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq17 eq163 -- forward demodulation 163,17
  have eq165 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq20 eq164 -- forward demodulation 164,20
  have eq166 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq118 eq165 -- forward demodulation 165,118
  have eq167 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq166 eq10 -- backward demodulation 10,166
  subsumption eq167 eq20


@[equational_result]
theorem Equation947_implies_Equation619 (G : Type*) [Magma G] (h : Equation947 G) : Equation619 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X3 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq20 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq17 eq9 -- backward demodulation 9,17
  have eq82 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq20 eq17 -- superposition 17,20, 20 into 17, unify on (0).2 in 20 and (0).1.2 in 17
  have eq93 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).1.2 in 20
  have eq117 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq17 eq82 -- forward demodulation 82,17
  have eq118 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := superpose eq20 eq117 -- forward demodulation 117,20
  have eq154 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq93 eq17 -- superposition 17,93, 93 into 17, unify on (0).2 in 93 and (0).1.2 in 17
  have eq163 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq17 eq154 -- forward demodulation 154,17
  have eq164 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq17 eq163 -- forward demodulation 163,17
  have eq165 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq20 eq164 -- forward demodulation 164,20
  have eq166 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq118 eq165 -- forward demodulation 165,118
  have eq167 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq166 eq10 -- backward demodulation 10,166
  subsumption eq167 eq20


@[equational_result]
theorem Equation947_implies_Equation3897 (G : Type*) [Magma G] (h : Equation947 G) : Equation3897 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X3 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2)))) = (X4 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X4 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X1) ◇ (X3 ◇ X1)) ◇ (X4 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X1)))))) = (X5 ◇ ((X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X1)))) ◇ (X5 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X1)) ◇ (X4 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X1))))))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq15 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X2) = (X4 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X4 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X2)))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq20 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq17 eq9 -- backward demodulation 9,17
  have eq21 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X2)) = (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2))))) := superpose eq17 eq11 -- backward demodulation 11,17
  have eq22 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X2)) = (X0 ◇ ((X3 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2)) := superpose eq17 eq12 -- backward demodulation 12,17
  have eq23 (X0 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2)))) = (X4 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X4 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2))))))) := superpose eq17 eq13 -- backward demodulation 13,17
  have eq24 (X0 X1 X3 X4 X5 : G) : ((X3 ◇ (X1 ◇ X1)) ◇ (X4 ◇ (X1 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X1)))))) = (X5 ◇ ((X1 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X5 ◇ ((X3 ◇ (X1 ◇ X1)) ◇ (X4 ◇ (X1 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X1))))))))) := superpose eq17 eq14 -- backward demodulation 14,17
  have eq25 (X0 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2) = (X4 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X4 ◇ ((X3 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2)))) := superpose eq17 eq15 -- backward demodulation 15,17
  have eq29 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq20 eq20 -- superposition 20,20, 20 into 20, unify on (0).2 in 20 and (0).1.2 in 20
  have eq30 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq29 eq20 -- superposition 20,29, 29 into 20, unify on (0).2 in 29 and (0).1.2 in 20
  have eq31 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq17 eq30 -- forward demodulation 30,17
  have eq34 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq21 eq21 -- superposition 21,21, 21 into 21, unify on (0).2 in 21 and (0).2.2.2 in 21
  have eq35 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq29 eq21 -- superposition 21,29, 29 into 21, unify on (0).2 in 29 and (0).2.2.2 in 21
  have eq37 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq21 eq21 -- superposition 21,21, 21 into 21, unify on (0).2 in 21 and (0).2.2 in 21
  have eq39 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq17 eq34 -- forward demodulation 34,17
  have eq40 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq17 eq39 -- forward demodulation 39,17
  have eq41 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) := superpose eq17 eq35 -- forward demodulation 35,17
  have eq42 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq17 eq41 -- forward demodulation 41,17
  have eq43 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq17 eq37 -- forward demodulation 37,17
  have eq44 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq20 eq43 -- forward demodulation 43,20
  have eq45 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq20 eq44 -- superposition 44,20, 20 into 44, unify on (0).2 in 20 and (0).1.2 in 44
  have eq47 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq17 eq45 -- forward demodulation 45,17
  have eq53 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))))) := superpose eq22 eq21 -- superposition 21,22, 22 into 21, unify on (0).2 in 22 and (0).2.2 in 21
  have eq60 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose eq17 eq53 -- forward demodulation 53,17
  have eq61 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq17 eq60 -- forward demodulation 60,17
  have eq76 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))))) = ((X2 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))))) := superpose eq21 eq17 -- superposition 17,21, 21 into 17, unify on (0).2 in 21 and (0).1.1 in 17
  have eq77 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2) ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2))) = ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2))) := superpose eq22 eq17 -- superposition 17,22, 22 into 17, unify on (0).2 in 22 and (0).1.1 in 17
  have eq82 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq20 eq17 -- superposition 17,20, 20 into 17, unify on (0).2 in 20 and (0).1.2 in 17
  have eq93 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).1.2 in 20
  have eq103 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).1.2.2 in 20
  have eq106 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))))) = (X3 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))))) := superpose eq17 eq76 -- forward demodulation 76,17
  have eq107 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))))) = (X3 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1)))))) := superpose eq17 eq106 -- forward demodulation 106,17
  have eq108 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))))) = (X3 ◇ (X1 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))))) := superpose eq17 eq107 -- forward demodulation 107,17
  have eq109 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))))) = (X3 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq17 eq108 -- forward demodulation 108,17
  have eq110 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X1 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) = (X5 ◇ ((X1 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X5 ◇ (X4 ◇ (X1 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1))))))))) := superpose eq109 eq24 -- backward demodulation 24,109
  have eq111 (X0 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2)))) = (X4 ◇ (X4 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2))))))) := superpose eq109 eq23 -- backward demodulation 23,109
  have eq112 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2))) = (X3 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2))) := superpose eq17 eq77 -- forward demodulation 77,17
  have eq113 (X0 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2) = (X4 ◇ (X4 ◇ ((X3 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2)))) := superpose eq112 eq25 -- backward demodulation 25,112
  have eq117 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq17 eq82 -- forward demodulation 82,17
  have eq118 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := superpose eq20 eq117 -- forward demodulation 117,20
  have eq121 (X0 X2 X3 X4 : G) : (X2 ◇ X2) = (X4 ◇ (X4 ◇ ((X3 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2)))) := superpose eq118 eq113 -- backward demodulation 113,118
  have eq122 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2))) = ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X2 ◇ X2))) := superpose eq118 eq112 -- backward demodulation 112,118
  have eq123 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2))) = (X3 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) := superpose eq17 eq122 -- forward demodulation 122,17
  have eq124 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2))) = (X3 ◇ (X2 ◇ (X2 ◇ X2))) := superpose eq17 eq123 -- forward demodulation 123,17
  have eq125 (X2 X4 : G) : (X2 ◇ X2) = (X4 ◇ (X4 ◇ (X2 ◇ (X2 ◇ X2)))) := superpose eq124 eq121 -- backward demodulation 121,124
  have eq144 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq20 eq93 -- superposition 93,20, 20 into 93, unify on (0).2 in 20 and (0).1.1 in 93
  have eq154 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq93 eq17 -- superposition 17,93, 93 into 17, unify on (0).2 in 93 and (0).1.2 in 17
  have eq156 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq103 eq144 -- forward demodulation 144,103
  have eq163 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq17 eq154 -- forward demodulation 154,17
  have eq164 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq17 eq163 -- forward demodulation 163,17
  have eq165 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq20 eq164 -- forward demodulation 164,20
  have eq166 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq118 eq165 -- forward demodulation 165,118
  have eq174 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq31 eq20 -- superposition 20,31, 31 into 20, unify on (0).2 in 31 and (0).1.2.2 in 20
  have eq182 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq31 eq17 -- superposition 17,31, 31 into 17, unify on (0).2 in 31 and (0).1.1 in 17
  have eq190 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq182 eq61 -- backward demodulation 61,182
  have eq191 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq182 eq42 -- backward demodulation 42,182
  have eq192 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq182 eq40 -- backward demodulation 40,182
  have eq273 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq174 eq174 -- superposition 174,174, 174 into 174, unify on (0).2 in 174 and (0).1 in 174
  have eq276 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) = ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) := superpose eq17 eq174 -- superposition 174,17, 17 into 174, unify on (0).2 in 17 and (0).2.2 in 174
  have eq283 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq174 eq20 -- superposition 20,174, 174 into 20, unify on (0).2 in 174 and (0).1.2 in 20
  have eq289 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq174 eq93 -- superposition 93,174, 174 into 93, unify on (0).2 in 174 and (0).1.2 in 93
  have eq305 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) = ((X2 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq17 eq276 -- forward demodulation 276,17
  have eq533 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq20 eq191 -- superposition 191,20, 20 into 191, unify on (0).2 in 20 and (0).2.1.2 in 191
  have eq577 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq17 eq533 -- forward demodulation 533,17
  have eq583 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X1 ◇ X1))) = ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq577 eq305 -- backward demodulation 305,577
  have eq693 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X1))) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq17 eq156 -- superposition 156,17, 17 into 156, unify on (0).2 in 17 and (0).1.2 in 156
  have eq717 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq156 eq20 -- superposition 20,156, 156 into 20, unify on (0).2 in 156 and (0).1.2 in 20
  have eq1025 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq717 eq190 -- superposition 190,717, 717 into 190, unify on (0).2 in 717 and (0).2.1 in 190
  have eq1047 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq17 eq1025 -- forward demodulation 1025,17
  have eq1167 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ (X1 ◇ X1))) = (X3 ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))))) := superpose eq21 eq273 -- superposition 273,21, 21 into 273, unify on (0).2 in 21 and (0).1.2 in 273
  have eq1238 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq273 eq190 -- superposition 190,273, 273 into 190, unify on (0).2 in 273 and (0).2.1 in 190
  have eq1424 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1))))))) := superpose eq190 eq111 -- superposition 111,190, 190 into 111, unify on (0).2 in 190 and (0).2.2 in 111
  have eq1428 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) ◇ (X3 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3)))) ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))))) := superpose eq17 eq111 -- superposition 111,17, 17 into 111, unify on (0).2 in 17 and (0).2.2 in 111
  have eq1456 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) = (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) := superpose eq111 eq17 -- superposition 17,111, 111 into 17, unify on (0).2 in 111 and (0).1.1 in 17
  have eq1653 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1))))))) := superpose eq17 eq1424 -- forward demodulation 1424,17
  have eq1654 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) ◇ (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))))))) := superpose eq17 eq1653 -- forward demodulation 1653,17
  have eq1655 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))))) := superpose eq17 eq1654 -- forward demodulation 1654,17
  have eq1656 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))))))) := superpose eq1047 eq1655 -- forward demodulation 1655,1047
  have eq1657 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))))) := superpose eq166 eq1656 -- forward demodulation 1656,166
  have eq1658 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) := superpose eq20 eq1657 -- forward demodulation 1657,20
  have eq1679 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) ◇ (X3 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X3))) ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))))) := superpose eq17 eq1428 -- forward demodulation 1428,17
  have eq1680 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X3 ◇ X3))))))) := superpose eq17 eq1679 -- forward demodulation 1679,17
  have eq1681 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3))))))) := superpose eq17 eq1680 -- forward demodulation 1680,17
  have eq1682 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ ((X3 ◇ X3) ◇ X3))))))) := superpose eq1047 eq1681 -- forward demodulation 1681,1047
  have eq1683 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X3))))))) := superpose eq166 eq1682 -- forward demodulation 1682,166
  have eq1684 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq20 eq1683 -- forward demodulation 1683,20
  have eq1772 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) = (X4 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1))))) ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) := superpose eq17 eq1456 -- forward demodulation 1456,17
  have eq1773 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) = (X4 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) := superpose eq17 eq1772 -- forward demodulation 1772,17
  have eq1774 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) := superpose eq17 eq1773 -- forward demodulation 1773,17
  have eq1775 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))))))) := superpose eq17 eq1774 -- forward demodulation 1774,17
  have eq1776 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))))))) := superpose eq17 eq1775 -- forward demodulation 1775,17
  have eq1777 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1)))))))) := superpose eq1047 eq1776 -- forward demodulation 1776,1047
  have eq1778 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))))) := superpose eq166 eq1777 -- forward demodulation 1777,166
  have eq1779 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1))))) := superpose eq20 eq1778 -- forward demodulation 1778,20
  have eq1780 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X1 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) = (X5 ◇ (X5 ◇ (X4 ◇ (X1 ◇ (X0 ◇ (X3 ◇ X1)))))) := superpose eq1779 eq110 -- backward demodulation 110,1779
  have eq1817 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq273 eq289 -- superposition 289,273, 273 into 289, unify on (0).2 in 273 and (0).1.1 in 289
  have eq2007 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X4 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))))) = (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)))))))) := superpose eq1780 eq1780 -- superposition 1780,1780, 1780 into 1780, unify on (0).2 in 1780 and (0).1.2.2 in 1780
  have eq2023 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))))) = (X4 ◇ (X4 ◇ (X3 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X1)))))) := superpose eq17 eq1780 -- superposition 1780,17, 17 into 1780, unify on (0).2 in 17 and (0).1.2.2 in 1780
  have eq2041 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) = (X4 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))))) := superpose eq190 eq1780 -- superposition 1780,190, 190 into 1780, unify on (0).2 in 190 and (0).1 in 1780
  have eq2049 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))))) = (X4 ◇ (X4 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X1 ◇ X1)))))) := superpose eq125 eq1780 -- superposition 1780,125, 125 into 1780, unify on (0).2 in 125 and (0).2.2.2.2.2.2 in 1780
  have eq2178 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) = (X4 ◇ (X4 ◇ (X3 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))))))) := superpose eq1780 eq20 -- superposition 20,1780, 1780 into 20, unify on (0).2 in 1780 and (0).1.2.2 in 20
  have eq2318 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X4 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))))) = (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq283 eq2007 -- forward demodulation 2007,283
  have eq2319 (X0 X1 X3 X4 : G) : (X3 ◇ (X0 ◇ X1)) = (X4 ◇ (X4 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))))) := superpose eq1817 eq2318 -- forward demodulation 2318,1817
  have eq2320 (X0 X1 X3 X4 : G) : (X3 ◇ (X0 ◇ X1)) = (X4 ◇ (X4 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1))))) := superpose eq20 eq2319 -- forward demodulation 2319,20
  have eq2321 (X0 X1 X3 X4 : G) : (X3 ◇ (X0 ◇ X1)) = (X4 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq1238 eq2320 -- forward demodulation 2320,1238
  have eq2394 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))))) = (X4 ◇ (X4 ◇ (X3 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X1)))))) := superpose eq17 eq2023 -- forward demodulation 2023,17
  have eq2395 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1)))))) = (X4 ◇ (X4 ◇ (X3 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X1)))))) := superpose eq1047 eq2394 -- forward demodulation 2394,1047
  have eq2396 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))) = (X4 ◇ (X4 ◇ (X3 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X1)))))) := superpose eq166 eq2395 -- forward demodulation 2395,166
  have eq2397 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X1))) = (X4 ◇ (X4 ◇ (X3 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X1)))))) := superpose eq20 eq2396 -- forward demodulation 2396,20
  have eq2434 (X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) = (X4 ◇ (X4 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))))) := superpose eq1658 eq2041 -- forward demodulation 2041,1658
  have eq2435 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X1))) = (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq1167 eq2434 -- forward demodulation 2434,1167
  have eq2436 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X1))) = (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq17 eq2435 -- forward demodulation 2435,17
  have eq2437 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq17 eq2436 -- forward demodulation 2436,17
  have eq2438 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))))) := superpose eq17 eq2437 -- forward demodulation 2437,17
  have eq2439 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1)))))) := superpose eq1047 eq2438 -- forward demodulation 2438,1047
  have eq2440 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq166 eq2439 -- forward demodulation 2439,166
  have eq2441 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq20 eq2440 -- forward demodulation 2440,20
  have eq2480 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))))) = (X4 ◇ (X4 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X1)))))) := superpose eq2441 eq2049 -- forward demodulation 2049,2441
  have eq2481 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X1))) = (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))))) := superpose eq2397 eq2480 -- forward demodulation 2480,2397
  have eq2482 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X1))) = (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))))))))) := superpose eq693 eq2481 -- forward demodulation 2481,693
  have eq2483 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X1))) = (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))))))))) := superpose eq583 eq2482 -- forward demodulation 2482,583
  have eq2484 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X1))) = (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq103 eq2483 -- forward demodulation 2483,103
  have eq2485 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X1))) = (X2 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq583 eq2484 -- forward demodulation 2484,583
  have eq2486 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X1))) = (X2 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))))) := superpose eq693 eq2485 -- forward demodulation 2485,693
  have eq2487 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X1))) = (X2 ◇ (X3 ◇ (X1 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))))) := superpose eq583 eq2486 -- forward demodulation 2486,583
  have eq2488 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X1))) = (X2 ◇ (X3 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq583 eq2487 -- forward demodulation 2487,583
  have eq2489 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X1))) = (X2 ◇ (X3 ◇ ((X1 ◇ X1) ◇ X1))) := superpose eq182 eq2488 -- forward demodulation 2488,182
  have eq2490 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X1))) = (X2 ◇ (X1 ◇ (X3 ◇ X1))) := superpose eq166 eq2489 -- forward demodulation 2489,166
  have eq2911 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) = (X4 ◇ (X4 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))))))) := superpose eq1684 eq2178 -- forward demodulation 2178,1684
  have eq2912 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) = (X4 ◇ (X4 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) := superpose eq1167 eq2911 -- forward demodulation 2911,1167
  have eq2913 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq2321 eq2912 -- forward demodulation 2912,2321
  have eq2915 (X0 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2)))) = (X4 ◇ (X4 ◇ (X3 ◇ (X0 ◇ X2)))) := superpose eq2913 eq111 -- backward demodulation 111,2913
  have eq2932 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1))))) = ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X4 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X1))))) := superpose eq2913 eq1779 -- backward demodulation 1779,2913
  have eq3658 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = ((X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := superpose eq2915 eq17 -- superposition 17,2915, 2915 into 17, unify on (0).2 in 2915 and (0).1.1 in 17
  have eq4091 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X3))))) = (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := superpose eq2932 eq3658 -- forward demodulation 3658,2932
  have eq4092 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X3))))) = (X4 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X2 ◇ X3))))) := superpose eq17 eq4091 -- forward demodulation 4091,17
  have eq4093 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X3))))) = (X4 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3))))) := superpose eq17 eq4092 -- forward demodulation 4092,17
  have eq4094 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X3))))) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) := superpose eq17 eq4093 -- forward demodulation 4093,17
  have eq4698 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq17 eq103 -- superposition 103,17, 17 into 103, unify on (0).2 in 17 and (0).2.2 in 103
  have eq4828 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1)))) := superpose eq2490 eq4698 -- forward demodulation 4698,2490
  have eq4829 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq166 eq4828 -- forward demodulation 4828,166
  have eq5843 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2))))) ◇ X2) = (((X0 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2))))) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2)))) := superpose eq118 eq192 -- superposition 192,118, 118 into 192, unify on (0).2 in 118 and (0).2.2 in 192
  have eq5917 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X2) = ((X0 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2))))) ◇ X2) := superpose eq4829 eq5843 -- forward demodulation 5843,4829
  have eq5918 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X2) = ((X0 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2))))) ◇ X2) := superpose eq4094 eq5917 -- forward demodulation 5917,4094
  have eq5919 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X2) = ((X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X2))))) ◇ X2) := superpose eq4094 eq5918 -- forward demodulation 5918,4094
  have eq5920 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))) ◇ X2) := superpose eq47 eq5919 -- forward demodulation 5919,47
  have eq5921 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq20 eq5920 -- forward demodulation 5920,20
  have eq6161 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq5921 eq10 -- superposition 10,5921, 5921 into 10, unify on (0).2 in 5921 and (0).2 in 10
  subsumption eq6161 rfl


@[equational_result]
theorem Equation947_implies_Equation1491 (G : Type*) [Magma G] (h : Equation947 G) : Equation1491 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X3 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq20 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq17 eq9 -- backward demodulation 9,17
  have eq29 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq20 eq20 -- superposition 20,20, 20 into 20, unify on (0).2 in 20 and (0).1.2 in 20
  have eq30 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq29 eq20 -- superposition 20,29, 29 into 20, unify on (0).2 in 29 and (0).1.2 in 20
  have eq31 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq17 eq30 -- forward demodulation 30,17
  have eq93 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).1.2 in 20
  have eq174 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq31 eq20 -- superposition 20,31, 31 into 20, unify on (0).2 in 31 and (0).1.2.2 in 20
  have eq186 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq174 eq10 -- backward demodulation 10,174
  subsumption eq186 eq93


@[equational_result]
theorem Equation947_implies_Equation723 (G : Type*) [Magma G] (h : Equation947 G) : Equation723 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK2 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X3 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq20 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq17 eq9 -- backward demodulation 9,17
  have eq82 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq20 eq17 -- superposition 17,20, 20 into 17, unify on (0).2 in 20 and (0).1.2 in 17
  have eq93 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).1.2 in 20
  have eq117 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq17 eq82 -- forward demodulation 82,17
  have eq118 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := superpose eq20 eq117 -- forward demodulation 117,20
  have eq154 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq93 eq17 -- superposition 17,93, 93 into 17, unify on (0).2 in 93 and (0).1.2 in 17
  have eq163 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq17 eq154 -- forward demodulation 154,17
  have eq164 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq17 eq163 -- forward demodulation 163,17
  have eq165 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq20 eq164 -- forward demodulation 164,20
  have eq166 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq118 eq165 -- forward demodulation 165,118
  have eq167 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq166 eq10 -- backward demodulation 10,166
  subsumption eq167 eq20


@[equational_result]
theorem Equation421_implies_Equation1224 (G : Type*) [Magma G] (h : Equation421 G) : Equation1224 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq17 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq16 -- forward demodulation 16,13
  subsumption eq17 eq12


@[equational_result]
theorem Equation421_implies_Equation418 (G : Type*) [Magma G] (h : Equation421 G) : Equation418 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation421_implies_Equation3660 (G : Type*) [Magma G] (h : Equation421 G) : Equation3660 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq16 eq12


@[equational_result]
theorem Equation421_implies_Equation3864 (G : Type*) [Magma G] (h : Equation421 G) : Equation3864 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 rfl


@[equational_result]
theorem Equation421_implies_Equation2036 (G : Type*) [Magma G] (h : Equation421 G) : Equation2036 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq17 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq16 -- forward demodulation 16,13
  subsumption eq17 eq12


@[equational_result]
theorem Equation421_implies_Equation823 (G : Type*) [Magma G] (h : Equation421 G) : Equation823 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq16 eq12


@[equational_result]
theorem Equation421_implies_Equation820 (G : Type*) [Magma G] (h : Equation421 G) : Equation820 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq16 eq12


@[equational_result]
theorem Equation421_implies_Equation4395 (G : Type*) [Magma G] (h : Equation421 G) : Equation4395 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq15 -- backward demodulation 15,13
  subsumption eq17 eq13


@[equational_result]
theorem Equation421_implies_Equation626 (G : Type*) [Magma G] (h : Equation421 G) : Equation626 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1))) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation421_implies_Equation621 (G : Type*) [Magma G] (h : Equation421 G) : Equation621 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2))) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation421_implies_Equation425 (G : Type*) [Magma G] (h : Equation421 G) : Equation425 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation421_implies_Equation628 (G : Type*) [Magma G] (h : Equation421 G) : Equation628 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK3))) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation421_implies_Equation422 (G : Type*) [Magma G] (h : Equation421 G) : Equation422 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation455_implies_Equation842 (G : Type*) [Magma G] (h : Equation455 G) : Equation842 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation455_implies_Equation3319 (G : Type*) [Magma G] (h : Equation455 G) : Equation3319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 rfl


@[equational_result]
theorem Equation455_implies_Equation1028 (G : Type*) [Magma G] (h : Equation455 G) : Equation1028 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation455_implies_Equation414 (G : Type*) [Magma G] (h : Equation455 G) : Equation414 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation455_implies_Equation3862 (G : Type*) [Magma G] (h : Equation455 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq9 -- backward demodulation 9,12
  subsumption eq14 rfl


@[equational_result]
theorem Equation455_implies_Equation3662 (G : Type*) [Magma G] (h : Equation455 G) : Equation3662 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation455_implies_Equation3725 (G : Type*) [Magma G] (h : Equation455 G) : Equation3725 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation455_implies_Equation1053 (G : Type*) [Magma G] (h : Equation455 G) : Equation1053 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq32 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq32 rfl


@[equational_result]
theorem Equation455_implies_Equation8 (G : Type*) [Magma G] (h : Equation455 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq16 : sK0 ≠ sK0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq16 rfl


@[equational_result]
theorem Equation455_implies_Equation1049 (G : Type*) [Magma G] (h : Equation455 G) : Equation1049 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation455_implies_Equation1832 (G : Type*) [Magma G] (h : Equation455 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq9 -- backward demodulation 9,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation455_implies_Equation4341 (G : Type*) [Magma G] (h : Equation455 G) : Equation4341 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation455_implies_Equation846 (G : Type*) [Magma G] (h : Equation455 G) : Equation846 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation258_implies_Equation2850 (G : Type*) [Magma G] (h : Equation258 G) : Equation2850 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq12 eq9


@[equational_result]
theorem Equation258_implies_Equation3253 (G : Type*) [Magma G] (h : Equation258 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq10 eq9 -- backward demodulation 9,10
  subsumption eq11 eq10


@[equational_result]
theorem Equation258_implies_Equation3459 (G : Type*) [Magma G] (h : Equation258 G) : Equation3459 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq15 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq29 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X2) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq31 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.2 in 13
  have eq92 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ X0) ◇ X0)) := superpose eq29 eq10 -- superposition 10,29, 29 into 10, unify on (0).2 in 29 and (0).2.2 in 10
  subsumption eq92 eq31


@[equational_result]
theorem Equation258_implies_Equation3456 (G : Type*) [Magma G] (h : Equation258 G) : Equation3456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1 in 8
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1 in 8
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.1 in 8
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq29 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).2.2 in 12
  have eq91 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ X0) ◇ X0)) := superpose eq24 eq9 -- superposition 9,24, 24 into 9, unify on (0).2 in 24 and (0).2.2 in 9
  subsumption eq91 eq29


@[equational_result]
theorem Equation258_implies_Equation263 (G : Type*) [Magma G] (h : Equation258 G) : Equation263 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq13 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq26 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := superpose eq14 eq13 -- superposition 13,14, 14 into 13, unify on (0).2 in 14 and (0).1.1 in 13
  have eq47 : sK0 ≠ sK0 := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation258_implies_Equation2663 (G : Type*) [Magma G] (h : Equation258 G) : Equation2663 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq15 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X2) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).1.1.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1.1 in 25
  have eq195 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X2) ◇ X2) := superpose eq15 eq39 -- superposition 39,15, 15 into 39, unify on (0).2 in 15 and (0).2.1.1.1 in 39
  have eq257 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq57 eq195 -- forward demodulation 195,57
  have eq258 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq257 eq10 -- backward demodulation 10,257
  subsumption eq258 eq9


@[equational_result]
theorem Equation3912_implies_Equation4068 (G : Type*) [Magma G] (h : Equation3912 G) : Equation4068 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq15 (X3 X4 X5 : G) : (X5 ◇ X5) = ((X4 ◇ X4) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq52 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq52 eq15


@[equational_result]
theorem Equation3912_implies_Equation4067 (G : Type*) [Magma G] (h : Equation3912 G) : Equation4067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq15 (X3 X4 X5 : G) : (X5 ◇ X5) = ((X4 ◇ X4) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq53 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq53 eq15


@[equational_result]
theorem Equation3912_implies_Equation4090 (G : Type*) [Magma G] (h : Equation3912 G) : Equation4090 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq15 (X3 X4 X5 : G) : (X5 ◇ X5) = ((X4 ◇ X4) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq52 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq52 eq15


@[equational_result]
theorem Equation3912_implies_Equation4066 (G : Type*) [Magma G] (h : Equation3912 G) : Equation4066 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq15 (X3 X4 X5 : G) : (X5 ◇ X5) = ((X4 ◇ X4) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq58 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq58 eq15


@[equational_result]
theorem Equation3912_implies_Equation359 (G : Type*) [Magma G] (h : Equation3912 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X3) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq14 (X3 X4 X5 : G) : (X5 ◇ X5) = ((X4 ◇ X4) ◇ X3) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1 in 8
  have eq15 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2 in 8
  have eq25 (X0 : G) : (X0 ◇ X0) ≠ ((X0 ◇ X0) ◇ sK0) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).1 in 9
  subsumption eq25 eq14


@[equational_result]
theorem Equation3912_implies_Equation3890 (G : Type*) [Magma G] (h : Equation3912 G) : Equation3890 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X2 X3 X4 X5 : G) : (X4 ◇ X4) = ((X5 ◇ (X3 ◇ X3)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq23 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ (X0 ◇ X0)) ◇ sK0) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1.2 in 10
  subsumption eq23 eq13


@[equational_result]
theorem Equation3912_implies_Equation4597 (G : Type*) [Magma G] (h : Equation3912 G) : Equation4597 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X3) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq15 (X3 X4 X5 : G) : (X5 ◇ X5) = ((X4 ◇ X4) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq52 (X0 : G) : (X0 ◇ X0) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq52 eq15


@[equational_result]
theorem Equation3912_implies_Equation4608 (G : Type*) [Magma G] (h : Equation3912 G) : Equation4608 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X3) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq15 (X3 X4 X5 : G) : (X5 ◇ X5) = ((X4 ◇ X4) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq52 (X0 : G) : (X0 ◇ X0) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq52 eq15


@[equational_result]
theorem Equation3912_implies_Equation3687 (G : Type*) [Magma G] (h : Equation3912 G) : Equation3687 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq15 (X3 X4 X5 : G) : (X5 ◇ X5) = ((X4 ◇ X4) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq23 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (sK1 ◇ sK0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1 in 10
  subsumption eq23 eq15


@[equational_result]
theorem Equation3912_implies_Equation3685 (G : Type*) [Magma G] (h : Equation3912 G) : Equation3685 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq15 (X3 X4 X5 : G) : (X5 ◇ X5) = ((X4 ◇ X4) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (sK0 ◇ sK1)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1 in 10
  subsumption eq26 eq15


@[equational_result]
theorem Equation3912_implies_Equation4091 (G : Type*) [Magma G] (h : Equation3912 G) : Equation4091 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq15 (X3 X4 X5 : G) : (X5 ◇ X5) = ((X4 ◇ X4) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq53 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq53 eq15


@[equational_result]
theorem Equation3912_implies_Equation3872 (G : Type*) [Magma G] (h : Equation3912 G) : Equation3872 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq13 (X2 X3 X4 X5 : G) : (X4 ◇ X4) = ((X5 ◇ (X3 ◇ X3)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK0 ◇ (X0 ◇ X0)) ◇ sK2) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1.2 in 10
  subsumption eq26 eq13


@[equational_result]
theorem Equation3912_implies_Equation3863 (G : Type*) [Magma G] (h : Equation3912 G) : Equation3863 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq13 (X2 X3 X4 X5 : G) : (X4 ◇ X4) = ((X5 ◇ (X3 ◇ X3)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq23 (X0 : G) : (X0 ◇ X0) ≠ ((sK0 ◇ (X0 ◇ X0)) ◇ sK1) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).1 in 10
  subsumption eq23 eq13


@[equational_result]
theorem Equation3912_implies_Equation3663 (G : Type*) [Magma G] (h : Equation3912 G) : Equation3663 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq15 (X3 X4 X5 : G) : (X5 ◇ X5) = ((X4 ◇ X4) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq26 (X0 : G) : (X0 ◇ X0) ≠ ((X0 ◇ X0) ◇ (sK1 ◇ sK2)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).1 in 10
  subsumption eq26 eq15


@[equational_result]
theorem Equation2347_implies_Equation2567 (G : Type*) [Magma G] (h : Equation2347 G) : Equation2567 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X3 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation2347_implies_Equation228 (G : Type*) [Magma G] (h : Equation2347 G) : Equation228 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X3 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq22 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation3324_implies_Equation3459 (G : Type*) [Magma G] (h : Equation3324 G) : Equation3459 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ X0) = (X4 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation3324_implies_Equation3521 (G : Type*) [Magma G] (h : Equation3324 G) : Equation3521 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ X0) = (X4 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation3324_implies_Equation3519 (G : Type*) [Magma G] (h : Equation3324 G) : Equation3519 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ X0) = (X4 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation3324_implies_Equation308 (G : Type*) [Magma G] (h : Equation3324 G) : Equation308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ X0) = (X4 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation3324_implies_Equation325 (G : Type*) [Magma G] (h : Equation3324 G) : Equation325 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ X0) = (X4 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation3324_implies_Equation3518 (G : Type*) [Magma G] (h : Equation3324 G) : Equation3518 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ X0) = (X4 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation3324_implies_Equation3526 (G : Type*) [Magma G] (h : Equation3324 G) : Equation3526 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ X0) = (X4 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation3324_implies_Equation4314 (G : Type*) [Magma G] (h : Equation3324 G) : Equation4314 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ X0) = (X4 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq14 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation3324_implies_Equation3458 (G : Type*) [Magma G] (h : Equation3324 G) : Equation3458 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ X0) = (X4 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation3324_implies_Equation3457 (G : Type*) [Magma G] (h : Equation3324 G) : Equation3457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ X0) = (X4 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation3324_implies_Equation3523 (G : Type*) [Magma G] (h : Equation3324 G) : Equation3523 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ X0) = (X4 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation3324_implies_Equation3520 (G : Type*) [Magma G] (h : Equation3324 G) : Equation3520 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ X0) = (X4 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation3324_implies_Equation3460 (G : Type*) [Magma G] (h : Equation3324 G) : Equation3460 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ X0) = (X4 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation3324_implies_Equation3525 (G : Type*) [Magma G] (h : Equation3324 G) : Equation3525 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ X0) = (X4 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation3324_implies_Equation3524 (G : Type*) [Magma G] (h : Equation3324 G) : Equation3524 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ X0) = (X4 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation3324_implies_Equation3527 (G : Type*) [Magma G] (h : Equation3324 G) : Equation3527 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ X0) = (X4 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation3324_implies_Equation4357 (G : Type*) [Magma G] (h : Equation3324 G) : Equation4357 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ X0) = (X4 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq14 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation3324_implies_Equation327 (G : Type*) [Magma G] (h : Equation3324 G) : Equation327 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ X0) = (X4 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2895_implies_Equation2072 (G : Type*) [Magma G] (h : Equation2895 G) : Equation2072 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X4 X5 : G) : (X4 ◇ X0) = (X4 ◇ X5) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq26 (X0 X1 X3 X4 : G) : (((X0 ◇ X3) ◇ X4) ◇ X1) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq74 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK2) ◇ (sK0 ◇ sK2)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.1.1 in 10
  subsumption eq74 eq26


@[equational_result]
theorem Equation2895_implies_Equation3529 (G : Type*) [Magma G] (h : Equation2895 G) : Equation3529 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X4 X5 : G) : (X4 ◇ X0) = (X4 ◇ X5) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq27 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq27 eq14


@[equational_result]
theorem Equation2973_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2973 G) : Equation2035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.2 in 8
  have eq12 (X2 : G) : ((X2 ◇ X2) ◇ X2) = X2 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.1 in 10
  have eq14 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq18 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq9 -- backward demodulation 9,12
  have eq20 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq18 -- backward demodulation 18,14
  subsumption eq20 eq14


@[equational_result]
theorem Equation2973_implies_Equation3722 (G : Type*) [Magma G] (h : Equation2973 G) : Equation3722 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq15 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq20 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation2973_implies_Equation8 (G : Type*) [Magma G] (h : Equation2973 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.2 in 8
  have eq14 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq19 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq9 -- backward demodulation 9,14
  subsumption eq19 eq14


@[equational_result]
theorem Equation2973_implies_Equation3915 (G : Type*) [Magma G] (h : Equation2973 G) : Equation3915 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq15 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq20 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq21 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq20 -- forward demodulation 20,15
  subsumption eq21 rfl


@[equational_result]
theorem Equation2973_implies_Equation1832 (G : Type*) [Magma G] (h : Equation2973 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.2 in 8
  have eq14 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq19 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq14 eq9 -- backward demodulation 9,14
  have eq20 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq19 -- forward demodulation 19,14
  subsumption eq20 eq14


@[equational_result]
theorem Equation2973_implies_Equation411 (G : Type*) [Magma G] (h : Equation2973 G) : Equation411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq10 (X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.2 in 8
  have eq14 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq19 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq14 eq9 -- backward demodulation 9,14
  have eq20 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq14 eq19 -- forward demodulation 19,14
  have eq21 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq20 -- forward demodulation 20,14
  subsumption eq21 eq14


@[equational_result]
theorem Equation2973_implies_Equation3065 (G : Type*) [Magma G] (h : Equation2973 G) : Equation3065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation2973_implies_Equation151 (G : Type*) [Magma G] (h : Equation2973 G) : Equation151 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.2 in 8
  have eq14 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq19 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq9 -- backward demodulation 9,14
  subsumption eq19 eq14


@[equational_result]
theorem Equation2973_implies_Equation47 (G : Type*) [Magma G] (h : Equation2973 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.2 in 8
  have eq14 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq19 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq14 eq9 -- backward demodulation 9,14
  have eq20 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq19 -- forward demodulation 19,14
  subsumption eq20 eq14


@[equational_result]
theorem Equation2973_implies_Equation1426 (G : Type*) [Magma G] (h : Equation2973 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.2 in 8
  have eq14 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq19 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq14 eq9 -- backward demodulation 9,14
  have eq20 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq19 -- forward demodulation 19,14
  subsumption eq20 eq14


@[equational_result]
theorem Equation2973_implies_Equation1223 (G : Type*) [Magma G] (h : Equation2973 G) : Equation1223 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.2 in 8
  have eq12 : sK0 ≠ (sK0 ◇ sK0) := superpose eq10 eq9 -- backward demodulation 9,10
  have eq15 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq23 : sK0 ≠ sK0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  subsumption eq23 rfl


@[equational_result]
theorem Equation2973_implies_Equation99 (G : Type*) [Magma G] (h : Equation2973 G) : Equation99 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.2 in 8
  have eq12 (X2 : G) : ((X2 ◇ X2) ◇ X2) = X2 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.1 in 10
  have eq14 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq18 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq9 -- backward demodulation 9,12
  have eq23 : sK0 ≠ sK0 := superpose eq14 eq18 -- superposition 18,14, 14 into 18, unify on (0).2 in 14 and (0).2 in 18
  subsumption eq23 rfl


@[equational_result]
theorem Equation2973_implies_Equation375 (G : Type*) [Magma G] (h : Equation2973 G) : Equation375 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq15 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq20 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq20 rfl


@[equational_result]
theorem Equation2973_implies_Equation3 (G : Type*) [Magma G] (h : Equation2973 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq10 (X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.2 in 8
  have eq14 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq19 : sK0 ≠ sK0 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2 in 9
  subsumption eq19 rfl


@[equational_result]
theorem Equation2973_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2973 G) : Equation2644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.2 in 8
  have eq14 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq18 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq14 eq9 -- backward demodulation 9,14
  have eq20 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq18 -- forward demodulation 18,14
  subsumption eq20 eq14


@[equational_result]
theorem Equation2973_implies_Equation614 (G : Type*) [Magma G] (h : Equation2973 G) : Equation614 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq10 (X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.2 in 8
  have eq12 (X2 : G) : ((X2 ◇ X2) ◇ X2) = X2 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.1 in 10
  have eq14 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq18 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq9 -- backward demodulation 9,12
  have eq20 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq18 -- backward demodulation 18,14
  subsumption eq20 eq14


@[equational_result]
theorem Equation2973_implies_Equation203 (G : Type*) [Magma G] (h : Equation2973 G) : Equation203 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.2 in 8
  have eq14 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq19 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq14 eq9 -- backward demodulation 9,14
  have eq20 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq19 -- forward demodulation 19,14
  subsumption eq20 eq14


@[equational_result]
theorem Equation2973_implies_Equation3139 (G : Type*) [Magma G] (h : Equation2973 G) : Equation3139 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation2973_implies_Equation3102 (G : Type*) [Magma G] (h : Equation2973 G) : Equation3102 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq16 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq24 : sK0 ≠ sK0 := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).2 in 13
  subsumption eq24 rfl


@[equational_result]
theorem Equation2973_implies_Equation3176 (G : Type*) [Magma G] (h : Equation2973 G) : Equation3176 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK2) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation433_implies_Equation1241 (G : Type*) [Magma G] (h : Equation433 G) : Equation1241 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation433_implies_Equation1038 (G : Type*) [Magma G] (h : Equation433 G) : Equation1038 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation433_implies_Equation1248 (G : Type*) [Magma G] (h : Equation433 G) : Equation1248 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation433_implies_Equation3862 (G : Type*) [Magma G] (h : Equation433 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq9 -- backward demodulation 9,12
  subsumption eq13 rfl


@[equational_result]
theorem Equation433_implies_Equation1847 (G : Type*) [Magma G] (h : Equation433 G) : Equation1847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation433_implies_Equation99 (G : Type*) [Magma G] (h : Equation433 G) : Equation99 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq15 rfl


@[equational_result]
theorem Equation433_implies_Equation1041 (G : Type*) [Magma G] (h : Equation433 G) : Equation1041 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


