import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation3348_implies_Equation3493 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3493 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK2)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq33 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq29 eq29 -- superposition 29,29, 29 into 29, unify on (0).2 in 29 and (0).2.2 in 29
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq23 -- superposition 23,29, 29 into 23, unify on (0).2 in 29 and (0).2 in 23
  have eq93 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK1) := superpose eq33 eq14 -- superposition 14,33, 33 into 14, unify on (0).2 in 33 and (0).2 in 14
  have eq104 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq46 eq46 -- superposition 46,46, 46 into 46, unify on (0).2 in 46 and (0).1 in 46
  have eq123 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ X0) := superpose eq46 eq93 -- superposition 93,46, 46 into 93, unify on (0).2 in 46 and (0).2 in 93
  subsumption eq123 eq104


@[equational_result]
theorem Equation3348_implies_Equation4325 (G : Type*) [Magma G] (h : Equation3348 G) : Equation4325 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq26 : (sK1 ◇ (sK2 ◇ sK2)) ≠ (sK0 ◇ sK0) := superpose eq22 eq10 -- backward demodulation 10,22
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq22 eq28 -- forward demodulation 28,22
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq22 -- superposition 22,29, 29 into 22, unify on (0).2 in 29 and (0).2 in 22
  have eq104 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq46 eq46 -- superposition 46,46, 46 into 46, unify on (0).2 in 46 and (0).1 in 46
  have eq123 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ X0)) := superpose eq46 eq26 -- superposition 26,46, 46 into 26, unify on (0).2 in 46 and (0).1.2 in 26
  subsumption eq123 eq104


@[equational_result]
theorem Equation3348_implies_Equation3885 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3885 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq15 -- backward demodulation 15,23
  have eq27 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ sK2) := superpose eq23 eq10 -- backward demodulation 10,23
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq30 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq29 -- forward demodulation 29,23
  have eq48 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X0) := superpose eq30 eq23 -- superposition 23,30, 30 into 23, unify on (0).2 in 30 and (0).2 in 23
  have eq61 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq48 eq48 -- superposition 48,48, 48 into 48, unify on (0).2 in 48 and (0).1 in 48
  have eq74 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq48 eq27 -- superposition 27,48, 48 into 27, unify on (0).2 in 48 and (0).2 in 27
  subsumption eq74 eq61


@[equational_result]
theorem Equation3348_implies_Equation3882 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3882 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq15 -- backward demodulation 15,23
  have eq27 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ sK2) := superpose eq23 eq10 -- backward demodulation 10,23
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq30 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq29 -- forward demodulation 29,23
  have eq48 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq30 eq23 -- superposition 23,30, 30 into 23, unify on (0).2 in 30 and (0).2 in 23
  have eq61 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq48 eq48 -- superposition 48,48, 48 into 48, unify on (0).2 in 48 and (0).1 in 48
  have eq74 (X0 : G) : (sK0 ◇ sK0) ≠ (sK2 ◇ X0) := superpose eq48 eq27 -- superposition 27,48, 48 into 27, unify on (0).2 in 48 and (0).2 in 27
  subsumption eq74 eq61


@[equational_result]
theorem Equation3348_implies_Equation4107 (G : Type*) [Magma G] (h : Equation3348 G) : Equation4107 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK1) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) = ((X2 ◇ X1) ◇ X3) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 : (sK0 ◇ sK0) ≠ ((sK2 ◇ sK1) ◇ sK3) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) = (X1 ◇ X3) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq21 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq26 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq26 eq9 -- backward demodulation 9,26
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq26 eq18 -- backward demodulation 18,26
  have eq59 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq28 eq26 -- superposition 26,28, 28 into 26, unify on (0).2 in 28 and (0).2 in 26
  have eq60 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq26 -- superposition 26,29, 29 into 26, unify on (0).2 in 29 and (0).2 in 26
  have eq71 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ sK3) := superpose eq59 eq15 -- backward demodulation 15,59
  have eq136 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq60 eq60 -- superposition 60,60, 60 into 60, unify on (0).2 in 60 and (0).1 in 60
  have eq161 (X0 : G) : (sK0 ◇ sK0) ≠ (sK3 ◇ X0) := superpose eq60 eq71 -- superposition 71,60, 60 into 71, unify on (0).2 in 60 and (0).2 in 71
  subsumption eq161 eq136


@[equational_result]
theorem Equation3348_implies_Equation3300 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3300 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq26 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq22 eq10 -- backward demodulation 10,22
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq22 eq28 -- forward demodulation 28,22
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq22 -- superposition 22,29, 29 into 22, unify on (0).2 in 29 and (0).2 in 22
  have eq51 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq22 eq26 -- superposition 26,22, 22 into 26, unify on (0).2 in 22 and (0).2 in 26
  subsumption eq51 eq46


@[equational_result]
theorem Equation3348_implies_Equation3545 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3545 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq35 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq29 eq14 -- superposition 14,29, 29 into 14, unify on (0).2 in 29 and (0).2 in 14
  subsumption eq35 rfl


@[equational_result]
theorem Equation3348_implies_Equation3798 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3798 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK0) ◇ (sK3 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq19 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK3 ◇ sK1)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  subsumption eq19 eq23


@[equational_result]
theorem Equation3348_implies_Equation4164 (G : Type*) [Magma G] (h : Equation3348 G) : Equation4164 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq45 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq23 -- superposition 23,29, 29 into 23, unify on (0).2 in 29 and (0).2 in 23
  have eq58 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq45 eq45 -- superposition 45,45, 45 into 45, unify on (0).2 in 45 and (0).1 in 45
  have eq76 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq45 eq14 -- superposition 14,45, 45 into 14, unify on (0).2 in 45 and (0).1 in 14
  subsumption eq76 eq58


@[equational_result]
theorem Equation3348_implies_Equation3607 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3607 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq23 -- superposition 23,29, 29 into 23, unify on (0).2 in 29 and (0).2 in 23
  have eq51 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK0) := superpose eq23 eq14 -- superposition 14,23, 23 into 14, unify on (0).2 in 23 and (0).2 in 14
  subsumption eq51 eq46


@[equational_result]
theorem Equation3348_implies_Equation3927 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3927 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq19 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq15 -- backward demodulation 15,23
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq30 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq29 -- forward demodulation 29,23
  have eq48 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq30 eq23 -- superposition 23,30, 30 into 23, unify on (0).2 in 30 and (0).2 in 23
  have eq61 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq48 eq48 -- superposition 48,48, 48 into 48, unify on (0).2 in 48 and (0).1 in 48
  have eq74 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ X0) := superpose eq48 eq19 -- superposition 19,48, 48 into 19, unify on (0).2 in 48 and (0).2 in 19
  subsumption eq74 eq61


@[equational_result]
theorem Equation3348_implies_Equation3756 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3756 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq15 -- backward demodulation 15,23
  have eq27 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X0) ◇ X3) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq48 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq23 -- superposition 23,29, 29 into 23, unify on (0).2 in 29 and (0).2 in 23
  have eq68 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK2)) := superpose eq27 eq10 -- superposition 10,27, 27 into 10, unify on (0).2 in 27 and (0).2 in 10
  subsumption eq68 eq48


@[equational_result]
theorem Equation3348_implies_Equation4084 (G : Type*) [Magma G] (h : Equation3348 G) : Equation4084 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq24 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq25 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = ((X1 ◇ X1) ◇ X3) := superpose eq24 eq17 -- backward demodulation 17,24
  have eq26 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq24 eq16 -- backward demodulation 16,24
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X0) ◇ X3) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq26 -- forward demodulation 26,13
  have eq30 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq24 eq29 -- forward demodulation 29,24
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq30 eq24 -- superposition 24,30, 30 into 24, unify on (0).2 in 30 and (0).2 in 24
  have eq63 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK1) := superpose eq28 eq14 -- superposition 14,28, 28 into 14, unify on (0).2 in 28 and (0).2 in 14
  subsumption eq63 eq46


@[equational_result]
theorem Equation3348_implies_Equation3634 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3634 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK3 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq33 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq29 eq29 -- superposition 29,29, 29 into 29, unify on (0).2 in 29 and (0).2.2 in 29
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq23 -- superposition 23,29, 29 into 23, unify on (0).2 in 29 and (0).2 in 23
  have eq93 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK2) := superpose eq33 eq14 -- superposition 14,33, 33 into 14, unify on (0).2 in 33 and (0).2 in 14
  subsumption eq93 eq46


@[equational_result]
theorem Equation3348_implies_Equation39 (G : Type*) [Magma G] (h : Equation3348 G) : Equation39 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq27 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq22 eq27 -- forward demodulation 27,22
  have eq44 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq28 eq22 -- superposition 22,28, 28 into 22, unify on (0).2 in 28 and (0).2 in 22
  have eq85 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq44 eq10 -- superposition 10,44, 44 into 10, unify on (0).2 in 44 and (0).2 in 10
  subsumption eq85 eq44


@[equational_result]
theorem Equation3348_implies_Equation3667 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3667 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq27 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X0) ◇ X3) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq52 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq52 eq27


@[equational_result]
theorem Equation3348_implies_Equation3947 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3947 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK3)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq27 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK3) ◇ sK1) := superpose eq23 eq10 -- backward demodulation 10,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X0) ◇ X3) := superpose eq13 eq24 -- forward demodulation 24,13
  subsumption eq27 eq28


@[equational_result]
theorem Equation3348_implies_Equation3587 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3587 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq23 -- superposition 23,29, 29 into 23, unify on (0).2 in 29 and (0).2 in 23
  have eq104 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq46 eq46 -- superposition 46,46, 46 into 46, unify on (0).2 in 46 and (0).1 in 46
  have eq123 (X0 : G) : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ X0)) := superpose eq46 eq14 -- superposition 14,46, 46 into 14, unify on (0).2 in 46 and (0).2.2 in 14
  subsumption eq123 eq104


@[equational_result]
theorem Equation3348_implies_Equation4141 (G : Type*) [Magma G] (h : Equation3348 G) : Equation4141 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq21 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq22 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).2 in 15
  have eq26 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq26 eq9 -- backward demodulation 9,26
  have eq59 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq28 eq26 -- superposition 26,28, 28 into 26, unify on (0).2 in 28 and (0).2 in 26
  have eq97 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq59 eq22 -- superposition 22,59, 59 into 22, unify on (0).2 in 59 and (0).2 in 22
  subsumption eq97 rfl


@[equational_result]
theorem Equation3348_implies_Equation3546 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3546 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq37 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq29 eq14 -- superposition 14,29, 29 into 14, unify on (0).2 in 29 and (0).2 in 14
  subsumption eq37 rfl


@[equational_result]
theorem Equation3348_implies_Equation3494 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3494 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK3)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq33 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq29 eq29 -- superposition 29,29, 29 into 29, unify on (0).2 in 29 and (0).2.2 in 29
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq23 -- superposition 23,29, 29 into 23, unify on (0).2 in 29 and (0).2 in 23
  have eq93 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK1) := superpose eq33 eq14 -- superposition 14,33, 33 into 14, unify on (0).2 in 33 and (0).2 in 14
  have eq104 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq46 eq46 -- superposition 46,46, 46 into 46, unify on (0).2 in 46 and (0).1 in 46
  have eq123 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ X0) := superpose eq46 eq93 -- superposition 93,46, 46 into 93, unify on (0).2 in 46 and (0).2 in 93
  subsumption eq123 eq104


@[equational_result]
theorem Equation3348_implies_Equation371 (G : Type*) [Magma G] (h : Equation3348 G) : Equation371 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq15 -- backward demodulation 15,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq45 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq23 -- superposition 23,29, 29 into 23, unify on (0).2 in 29 and (0).2 in 23
  have eq58 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq45 eq45 -- superposition 45,45, 45 into 45, unify on (0).2 in 45 and (0).1 in 45
  have eq70 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ X0) := superpose eq45 eq10 -- superposition 10,45, 45 into 10, unify on (0).2 in 45 and (0).2 in 10
  subsumption eq70 eq58


@[equational_result]
theorem Equation3348_implies_Equation4337 (G : Type*) [Magma G] (h : Equation3348 G) : Equation4337 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq26 : (sK2 ◇ (sK3 ◇ sK3)) ≠ (sK0 ◇ sK0) := superpose eq22 eq10 -- backward demodulation 10,22
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq22 eq28 -- forward demodulation 28,22
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq22 -- superposition 22,29, 29 into 22, unify on (0).2 in 29 and (0).2 in 22
  have eq104 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq46 eq46 -- superposition 46,46, 46 into 46, unify on (0).2 in 46 and (0).1 in 46
  have eq123 (X0 : G) : (sK0 ◇ sK0) ≠ (sK2 ◇ (sK3 ◇ X0)) := superpose eq46 eq26 -- superposition 26,46, 46 into 26, unify on (0).2 in 46 and (0).1.2 in 26
  subsumption eq123 eq104


@[equational_result]
theorem Equation3348_implies_Equation3556 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3556 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq37 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq29 eq14 -- superposition 14,29, 29 into 14, unify on (0).2 in 29 and (0).2 in 14
  subsumption eq37 rfl


@[equational_result]
theorem Equation3348_implies_Equation3346 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3346 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq26 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq22 eq10 -- backward demodulation 10,22
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq22 eq28 -- forward demodulation 28,22
  subsumption eq26 eq29


@[equational_result]
theorem Equation3348_implies_Equation3770 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3770 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq15 -- backward demodulation 15,23
  have eq27 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X0) ◇ X3) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq72 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK2)) := superpose eq27 eq10 -- superposition 10,27, 27 into 10, unify on (0).2 in 27 and (0).2 in 10
  subsumption eq72 eq29


@[equational_result]
theorem Equation3348_implies_Equation319 (G : Type*) [Magma G] (h : Equation3348 G) : Equation319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq27 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq22 eq27 -- forward demodulation 27,22
  have eq45 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq28 eq22 -- superposition 22,28, 28 into 22, unify on (0).2 in 28 and (0).2 in 22
  have eq50 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).2 in 10
  have eq79 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq45 eq45 -- superposition 45,45, 45 into 45, unify on (0).2 in 45 and (0).1 in 45
  have eq95 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ X0) := superpose eq45 eq50 -- superposition 50,45, 45 into 50, unify on (0).2 in 45 and (0).2 in 50
  subsumption eq95 eq79


@[equational_result]
theorem Equation3348_implies_Equation335 (G : Type*) [Magma G] (h : Equation3348 G) : Equation335 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq27 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq22 eq27 -- forward demodulation 27,22
  have eq45 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq28 eq22 -- superposition 22,28, 28 into 22, unify on (0).2 in 28 and (0).2 in 22
  have eq46 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).2 in 10
  subsumption eq46 eq45


@[equational_result]
theorem Equation3348_implies_Equation318 (G : Type*) [Magma G] (h : Equation3348 G) : Equation318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq27 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq22 eq27 -- forward demodulation 27,22
  have eq45 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq28 eq22 -- superposition 22,28, 28 into 22, unify on (0).2 in 28 and (0).2 in 22
  have eq50 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).2 in 10
  subsumption eq50 eq45


@[equational_result]
theorem Equation3348_implies_Equation3352 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3352 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq26 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq22 eq10 -- backward demodulation 10,22
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq22 eq28 -- forward demodulation 28,22
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq22 -- superposition 22,29, 29 into 22, unify on (0).2 in 29 and (0).2 in 22
  have eq51 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq22 eq26 -- superposition 26,22, 22 into 26, unify on (0).2 in 22 and (0).2 in 26
  subsumption eq51 eq46


@[equational_result]
theorem Equation3348_implies_Equation3761 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3761 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq19 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq15 -- backward demodulation 15,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq48 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq23 -- superposition 23,29, 29 into 23, unify on (0).2 in 29 and (0).2 in 23
  have eq49 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq23 eq19 -- superposition 19,23, 23 into 19, unify on (0).2 in 23 and (0).2 in 19
  subsumption eq49 eq48


@[equational_result]
theorem Equation3348_implies_Equation4313 (G : Type*) [Magma G] (h : Equation3348 G) : Equation4313 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK3 ◇ sK4)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq26 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ sK4)) := superpose eq22 eq10 -- backward demodulation 10,22
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq22 eq28 -- forward demodulation 28,22
  have eq37 : (sK0 ◇ sK1) ≠ (sK3 ◇ sK2) := superpose eq29 eq26 -- superposition 26,29, 29 into 26, unify on (0).2 in 29 and (0).2 in 26
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq22 -- superposition 22,29, 29 into 22, unify on (0).2 in 29 and (0).2 in 22
  have eq104 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq46 eq46 -- superposition 46,46, 46 into 46, unify on (0).2 in 46 and (0).1 in 46
  have eq123 (X0 : G) : (sK0 ◇ sK1) ≠ (sK2 ◇ X0) := superpose eq46 eq37 -- superposition 37,46, 46 into 37, unify on (0).2 in 46 and (0).2 in 37
  subsumption eq123 eq104


@[equational_result]
theorem Equation3348_implies_Equation3620 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3620 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK2 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq23 -- superposition 23,29, 29 into 23, unify on (0).2 in 29 and (0).2 in 23
  have eq51 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK0) := superpose eq23 eq14 -- superposition 14,23, 23 into 14, unify on (0).2 in 23 and (0).2 in 14
  subsumption eq51 eq46


@[equational_result]
theorem Equation3348_implies_Equation4076 (G : Type*) [Magma G] (h : Equation3348 G) : Equation4076 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) = ((X2 ◇ X1) ◇ X3) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) = (X1 ◇ X3) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq21 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq26 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq26 eq9 -- backward demodulation 9,26
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq26 eq18 -- backward demodulation 18,26
  have eq59 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq28 eq26 -- superposition 26,28, 28 into 26, unify on (0).2 in 28 and (0).2 in 26
  have eq60 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq26 -- superposition 26,29, 29 into 26, unify on (0).2 in 29 and (0).2 in 26
  have eq87 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq59 eq15 -- superposition 15,59, 59 into 15, unify on (0).2 in 59 and (0).2 in 15
  subsumption eq87 eq60


@[equational_result]
theorem Equation3348_implies_Equation3932 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3932 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq15 -- backward demodulation 15,23
  have eq27 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK2) := superpose eq23 eq10 -- backward demodulation 10,23
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq30 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq29 -- forward demodulation 29,23
  have eq48 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq30 eq23 -- superposition 23,30, 30 into 23, unify on (0).2 in 30 and (0).2 in 23
  have eq61 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq48 eq48 -- superposition 48,48, 48 into 48, unify on (0).2 in 48 and (0).1 in 48
  have eq74 (X0 : G) : (sK0 ◇ sK1) ≠ (sK2 ◇ X0) := superpose eq48 eq27 -- superposition 27,48, 48 into 27, unify on (0).2 in 48 and (0).2 in 27
  subsumption eq74 eq61


@[equational_result]
theorem Equation3348_implies_Equation3398 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3398 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq23 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = ((X1 ◇ X1) ◇ X3) := superpose eq22 eq16 -- backward demodulation 16,22
  have eq24 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq26 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ sK2)) := superpose eq22 eq10 -- backward demodulation 10,22
  have eq27 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X0) ◇ X3) := superpose eq13 eq23 -- forward demodulation 23,13
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq22 eq28 -- forward demodulation 28,22
  have eq37 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK2) := superpose eq29 eq26 -- superposition 26,29, 29 into 26, unify on (0).2 in 29 and (0).2 in 26
  have eq46 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X0) := superpose eq29 eq22 -- superposition 22,29, 29 into 22, unify on (0).2 in 29 and (0).2 in 22
  have eq61 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X2) := superpose eq13 eq27 -- superposition 27,13, 13 into 27, unify on (0).2 in 13 and (0).2 in 27
  have eq123 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq46 eq37 -- superposition 37,46, 46 into 37, unify on (0).2 in 46 and (0).2 in 37
  subsumption eq123 eq61


@[equational_result]
theorem Equation3348_implies_Equation321 (G : Type*) [Magma G] (h : Equation3348 G) : Equation321 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq27 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq22 eq27 -- forward demodulation 27,22
  have eq36 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK1) := superpose eq28 eq10 -- superposition 10,28, 28 into 10, unify on (0).2 in 28 and (0).2 in 10
  have eq45 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq28 eq22 -- superposition 22,28, 28 into 22, unify on (0).2 in 28 and (0).2 in 22
  have eq79 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq45 eq45 -- superposition 45,45, 45 into 45, unify on (0).2 in 45 and (0).1 in 45
  have eq95 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ X0) := superpose eq45 eq36 -- superposition 36,45, 45 into 36, unify on (0).2 in 45 and (0).2 in 36
  subsumption eq95 eq79


@[equational_result]
theorem Equation3348_implies_Equation3355 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3355 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq26 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq22 eq10 -- backward demodulation 10,22
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq22 eq28 -- forward demodulation 28,22
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq22 -- superposition 22,29, 29 into 22, unify on (0).2 in 29 and (0).2 in 22
  have eq51 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq22 eq26 -- superposition 26,22, 22 into 26, unify on (0).2 in 22 and (0).2 in 26
  subsumption eq51 eq46


@[equational_result]
theorem Equation3348_implies_Equation3535 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3535 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK1) ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK3)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq33 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq29 eq29 -- superposition 29,29, 29 into 29, unify on (0).2 in 29 and (0).2.2 in 29
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq23 -- superposition 23,29, 29 into 23, unify on (0).2 in 29 and (0).2 in 23
  have eq93 : (sK0 ◇ sK1) ≠ (sK3 ◇ sK0) := superpose eq33 eq14 -- superposition 14,33, 33 into 14, unify on (0).2 in 33 and (0).2 in 14
  subsumption eq93 eq46


@[equational_result]
theorem Equation3348_implies_Equation4178 (G : Type*) [Magma G] (h : Equation3348 G) : Equation4178 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK2) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq21 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq22 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).2 in 15
  have eq26 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq26 eq9 -- backward demodulation 9,26
  have eq59 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq28 eq26 -- superposition 26,28, 28 into 26, unify on (0).2 in 28 and (0).2 in 26
  have eq97 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq59 eq22 -- superposition 22,59, 59 into 22, unify on (0).2 in 59 and (0).2 in 22
  subsumption eq97 rfl


@[equational_result]
theorem Equation3348_implies_Equation3565 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3565 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq35 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq29 eq14 -- superposition 14,29, 29 into 14, unify on (0).2 in 29 and (0).2 in 14
  subsumption eq35 rfl


@[equational_result]
theorem Equation3348_implies_Equation3718 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3718 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq19 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK1)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  subsumption eq19 eq23


@[equational_result]
theorem Equation3348_implies_Equation3933 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3933 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq15 -- backward demodulation 15,23
  have eq27 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK3) := superpose eq23 eq10 -- backward demodulation 10,23
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq30 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq29 -- forward demodulation 29,23
  have eq48 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq30 eq23 -- superposition 23,30, 30 into 23, unify on (0).2 in 30 and (0).2 in 23
  have eq61 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq48 eq48 -- superposition 48,48, 48 into 48, unify on (0).2 in 48 and (0).1 in 48
  have eq74 (X0 : G) : (sK0 ◇ sK1) ≠ (sK3 ◇ X0) := superpose eq48 eq27 -- superposition 27,48, 48 into 27, unify on (0).2 in 48 and (0).2 in 27
  subsumption eq74 eq61


@[equational_result]
theorem Equation3348_implies_Equation3320 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq26 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq22 eq10 -- backward demodulation 10,22
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq22 eq28 -- forward demodulation 28,22
  have eq33 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq29 eq29 -- superposition 29,29, 29 into 29, unify on (0).2 in 29 and (0).2.2 in 29
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq22 -- superposition 22,29, 29 into 22, unify on (0).2 in 29 and (0).2 in 22
  have eq93 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK0) := superpose eq33 eq26 -- superposition 26,33, 33 into 26, unify on (0).2 in 33 and (0).2 in 26
  subsumption eq93 eq46


@[equational_result]
theorem Equation3348_implies_Equation3549 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3549 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq35 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq29 eq14 -- superposition 14,29, 29 into 14, unify on (0).2 in 29 and (0).2 in 14
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq23 -- superposition 23,29, 29 into 23, unify on (0).2 in 29 and (0).2 in 23
  have eq96 (X0 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ X0) := superpose eq46 eq35 -- superposition 35,46, 46 into 35, unify on (0).2 in 46 and (0).2 in 35
  subsumption eq96 eq46


@[equational_result]
theorem Equation3348_implies_Equation3679 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3679 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq19 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq15 -- backward demodulation 15,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq48 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq23 -- superposition 23,29, 29 into 23, unify on (0).2 in 29 and (0).2 in 23
  have eq54 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK2) := superpose eq23 eq19 -- superposition 19,23, 23 into 19, unify on (0).2 in 23 and (0).2 in 19
  subsumption eq54 eq48


@[equational_result]
theorem Equation3348_implies_Equation4543 (G : Type*) [Magma G] (h : Equation3348 G) : Equation4543 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK0) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK3) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq27 : (sK0 ◇ sK3) ≠ (sK0 ◇ sK2) := superpose eq23 eq14 -- backward demodulation 14,23
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq30 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq29 -- forward demodulation 29,23
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq30 eq23 -- superposition 23,30, 30 into 23, unify on (0).2 in 30 and (0).2 in 23
  have eq79 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq46 eq46 -- superposition 46,46, 46 into 46, unify on (0).2 in 46 and (0).1 in 46
  have eq103 (X0 : G) : (sK0 ◇ sK2) ≠ (X0 ◇ sK0) := superpose eq46 eq27 -- superposition 27,46, 46 into 27, unify on (0).2 in 46 and (0).1 in 27
  subsumption eq103 eq79


@[equational_result]
theorem Equation3348_implies_Equation3930 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3930 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq19 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK2) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq15 -- backward demodulation 15,23
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq30 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq29 -- forward demodulation 29,23
  have eq48 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq30 eq23 -- superposition 23,30, 30 into 23, unify on (0).2 in 30 and (0).2 in 23
  have eq61 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq48 eq48 -- superposition 48,48, 48 into 48, unify on (0).2 in 48 and (0).1 in 48
  have eq74 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ X0) := superpose eq48 eq19 -- superposition 19,48, 48 into 19, unify on (0).2 in 48 and (0).2 in 19
  subsumption eq74 eq61


@[equational_result]
theorem Equation3348_implies_Equation3716 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3716 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq15 -- backward demodulation 15,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq36 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq29 eq10 -- superposition 10,29, 29 into 10, unify on (0).2 in 29 and (0).2 in 10
  subsumption eq36 eq29


@[equational_result]
theorem Equation3348_implies_Equation3481 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3481 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq23 -- superposition 23,29, 29 into 23, unify on (0).2 in 29 and (0).2 in 23
  have eq47 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq23 eq14 -- superposition 14,23, 23 into 14, unify on (0).2 in 23 and (0).2 in 14
  subsumption eq47 eq46


@[equational_result]
theorem Equation3348_implies_Equation4158 (G : Type*) [Magma G] (h : Equation3348 G) : Equation4158 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq24 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq25 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = ((X1 ◇ X1) ◇ X3) := superpose eq24 eq17 -- backward demodulation 17,24
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X0) ◇ X3) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq63 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq28 eq14 -- superposition 14,28, 28 into 14, unify on (0).2 in 28 and (0).2 in 14
  subsumption eq63 rfl


@[equational_result]
theorem Equation3348_implies_Equation3591 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3591 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK0 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq33 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq29 eq29 -- superposition 29,29, 29 into 29, unify on (0).2 in 29 and (0).2.2 in 29
  have eq46 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X0) := superpose eq29 eq23 -- superposition 23,29, 29 into 23, unify on (0).2 in 29 and (0).2 in 23
  have eq93 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK2) := superpose eq33 eq14 -- superposition 14,33, 33 into 14, unify on (0).2 in 33 and (0).2 in 14
  subsumption eq93 eq46


@[equational_result]
theorem Equation3348_implies_Equation313 (G : Type*) [Magma G] (h : Equation3348 G) : Equation313 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq27 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq22 eq27 -- forward demodulation 27,22
  have eq45 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq28 eq22 -- superposition 22,28, 28 into 22, unify on (0).2 in 28 and (0).2 in 22
  have eq50 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).2 in 10
  have eq79 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq45 eq45 -- superposition 45,45, 45 into 45, unify on (0).2 in 45 and (0).1 in 45
  have eq95 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ X0) := superpose eq45 eq50 -- superposition 50,45, 45 into 50, unify on (0).2 in 45 and (0).2 in 50
  subsumption eq95 eq79


@[equational_result]
theorem Equation3348_implies_Equation3654 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3654 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK3 ◇ sK4) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK4 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq33 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq29 eq29 -- superposition 29,29, 29 into 29, unify on (0).2 in 29 and (0).2.2 in 29
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq23 -- superposition 23,29, 29 into 23, unify on (0).2 in 29 and (0).2 in 23
  have eq93 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK2) := superpose eq33 eq14 -- superposition 14,33, 33 into 14, unify on (0).2 in 33 and (0).2 in 14
  subsumption eq93 eq46


@[equational_result]
theorem Equation3348_implies_Equation3683 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3683 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq19 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK2 ◇ sK3)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq15 -- backward demodulation 15,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq48 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq23 -- superposition 23,29, 29 into 23, unify on (0).2 in 29 and (0).2 in 23
  have eq54 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK3) := superpose eq23 eq19 -- superposition 19,23, 23 into 19, unify on (0).2 in 23 and (0).2 in 19
  subsumption eq54 eq48


@[equational_result]
theorem Equation3348_implies_Equation4102 (G : Type*) [Magma G] (h : Equation3348 G) : Equation4102 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) = ((X2 ◇ X1) ◇ X3) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 : (sK0 ◇ sK0) ≠ ((sK2 ◇ sK0) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) = (X1 ◇ X3) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq21 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq26 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq26 eq9 -- backward demodulation 9,26
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq26 eq18 -- backward demodulation 18,26
  have eq59 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq28 eq26 -- superposition 26,28, 28 into 26, unify on (0).2 in 28 and (0).2 in 26
  have eq60 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq26 -- superposition 26,29, 29 into 26, unify on (0).2 in 29 and (0).2 in 26
  have eq71 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK2) ◇ sK2) := superpose eq59 eq15 -- backward demodulation 15,59
  have eq136 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq60 eq60 -- superposition 60,60, 60 into 60, unify on (0).2 in 60 and (0).1 in 60
  have eq161 (X0 : G) : (sK0 ◇ sK0) ≠ (sK2 ◇ X0) := superpose eq60 eq71 -- superposition 71,60, 60 into 71, unify on (0).2 in 60 and (0).2 in 71
  subsumption eq161 eq136


@[equational_result]
theorem Equation3348_implies_Equation3929 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3929 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq15 -- backward demodulation 15,23
  have eq27 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq23 eq10 -- backward demodulation 10,23
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq30 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq29 -- forward demodulation 29,23
  have eq48 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq30 eq23 -- superposition 23,30, 30 into 23, unify on (0).2 in 30 and (0).2 in 23
  have eq61 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq48 eq48 -- superposition 48,48, 48 into 48, unify on (0).2 in 48 and (0).1 in 48
  have eq74 (X0 : G) : (sK0 ◇ sK1) ≠ (sK2 ◇ X0) := superpose eq48 eq27 -- superposition 27,48, 48 into 27, unify on (0).2 in 48 and (0).2 in 27
  subsumption eq74 eq61


@[equational_result]
theorem Equation3348_implies_Equation3886 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3886 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq15 -- backward demodulation 15,23
  have eq27 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ sK3) := superpose eq23 eq10 -- backward demodulation 10,23
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq30 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq29 -- forward demodulation 29,23
  have eq48 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X0) := superpose eq30 eq23 -- superposition 23,30, 30 into 23, unify on (0).2 in 30 and (0).2 in 23
  have eq61 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq48 eq48 -- superposition 48,48, 48 into 48, unify on (0).2 in 48 and (0).1 in 48
  have eq74 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq48 eq27 -- superposition 27,48, 48 into 27, unify on (0).2 in 48 and (0).2 in 27
  subsumption eq74 eq61


@[equational_result]
theorem Equation3348_implies_Equation4167 (G : Type*) [Magma G] (h : Equation3348 G) : Equation4167 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq24 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq26 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq24 eq16 -- backward demodulation 16,24
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq26 -- forward demodulation 26,13
  have eq30 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq24 eq29 -- forward demodulation 29,24
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq30 eq24 -- superposition 24,30, 30 into 24, unify on (0).2 in 30 and (0).2 in 24
  have eq80 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq46 eq46 -- superposition 46,46, 46 into 46, unify on (0).2 in 46 and (0).1 in 46
  have eq96 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ X0) := superpose eq46 eq14 -- superposition 14,46, 46 into 14, unify on (0).2 in 46 and (0).2 in 14
  subsumption eq96 eq80


@[equational_result]
theorem Equation3348_implies_Equation3823 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3823 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq15 -- backward demodulation 15,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq48 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq23 -- superposition 23,29, 29 into 23, unify on (0).2 in 29 and (0).2 in 23
  have eq52 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ sK0) := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq52 eq48


@[equational_result]
theorem Equation3348_implies_Equation3573 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3573 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK2 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq23 -- superposition 23,29, 29 into 23, unify on (0).2 in 29 and (0).2 in 23
  have eq51 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq23 eq14 -- superposition 14,23, 23 into 14, unify on (0).2 in 23 and (0).2 in 14
  subsumption eq51 eq46


@[equational_result]
theorem Equation2774_implies_Equation2306 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2306 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq29 (X0 X1 X4 : G) : ((X1 ◇ (X4 ◇ (X1 ◇ X0))) ◇ X4) = X4 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2.2 in 11
  have eq129 : sK0 ≠ sK0 := superpose eq29 eq10 -- superposition 10,29, 29 into 10, unify on (0).2 in 29 and (0).2 in 10
  subsumption eq129 rfl


@[equational_result]
theorem Equation2774_implies_Equation2449 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2449 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation2774_implies_Equation2469 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2469 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation2774_implies_Equation2253 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2774_implies_Equation2472 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2472 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2774_implies_Equation2476 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2476 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2774_implies_Equation2446 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2446 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2774_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2238 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq17 rfl


@[equational_result]
theorem Equation2774_implies_Equation2452 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2452 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2774_implies_Equation3519 (G : Type*) [Magma G] (h : Equation2774 G) : Equation3519 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq21 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq21 rfl


@[equational_result]
theorem Equation2774_implies_Equation2277 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2277 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2774_implies_Equation203 (G : Type*) [Magma G] (h : Equation2774 G) : Equation203 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq17 rfl


@[equational_result]
theorem Equation2774_implies_Equation3522 (G : Type*) [Magma G] (h : Equation2774 G) : Equation3522 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq21 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq21 rfl


@[equational_result]
theorem Equation2774_implies_Equation1644 (G : Type*) [Magma G] (h : Equation2774 G) : Equation1644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq21 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq21 eq14


@[equational_result]
theorem Equation2774_implies_Equation2456 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation2774_implies_Equation4138 (G : Type*) [Magma G] (h : Equation2774 G) : Equation4138 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq21 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq21 rfl


@[equational_result]
theorem Equation2774_implies_Equation3052 (G : Type*) [Magma G] (h : Equation2774 G) : Equation3052 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq21 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq21 eq14


@[equational_result]
theorem Equation2774_implies_Equation2459 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2459 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2774_implies_Equation4631 (G : Type*) [Magma G] (h : Equation2774 G) : Equation4631 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq21 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq21 eq14


@[equational_result]
theorem Equation2774_implies_Equation2263 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2263 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2774_implies_Equation2256 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2774_implies_Equation1650 (G : Type*) [Magma G] (h : Equation2774 G) : Equation1650 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq21 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq21 eq14


@[equational_result]
theorem Equation2774_implies_Equation1629 (G : Type*) [Magma G] (h : Equation2774 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 (X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = X3 := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).1.1.2 in 12
  have eq20 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq13 eq9 -- backward demodulation 9,13
  subsumption eq20 eq13


@[equational_result]
theorem Equation2774_implies_Equation2466 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2774_implies_Equation23 (G : Type*) [Magma G] (h : Equation2774 G) : Equation23 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 (X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = X3 := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).1.1.2 in 12
  have eq55 : sK0 ≠ sK0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2 in 9
  subsumption eq55 rfl


@[equational_result]
theorem Equation2774_implies_Equation3458 (G : Type*) [Magma G] (h : Equation2774 G) : Equation3458 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq21 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq21 rfl


@[equational_result]
theorem Equation2774_implies_Equation3068 (G : Type*) [Magma G] (h : Equation2774 G) : Equation3068 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq21 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq21 eq14


@[equational_result]
theorem Equation2774_implies_Equation3065 (G : Type*) [Magma G] (h : Equation2774 G) : Equation3065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq21 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq21 eq14


@[equational_result]
theorem Equation2774_implies_Equation2303 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2303 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq29 (X0 X1 X4 : G) : ((X1 ◇ (X4 ◇ (X1 ◇ X0))) ◇ X4) = X4 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2.2 in 11
  have eq129 : sK0 ≠ sK0 := superpose eq29 eq10 -- superposition 10,29, 29 into 10, unify on (0).2 in 29 and (0).2 in 10
  subsumption eq129 rfl


@[equational_result]
theorem Equation2774_implies_Equation2300 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2300 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq29 (X0 X1 X4 : G) : ((X1 ◇ (X4 ◇ (X1 ◇ X0))) ◇ X4) = X4 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2.2 in 11
  have eq129 : sK0 ≠ sK0 := superpose eq29 eq10 -- superposition 10,29, 29 into 10, unify on (0).2 in 29 and (0).2 in 10
  subsumption eq129 rfl


@[equational_result]
theorem Equation2774_implies_Equation3525 (G : Type*) [Magma G] (h : Equation2774 G) : Equation3525 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq21 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq21 rfl


@[equational_result]
theorem Equation2774_implies_Equation3071 (G : Type*) [Magma G] (h : Equation2774 G) : Equation3071 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq21 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq21 eq14


@[equational_result]
theorem Equation2774_implies_Equation2484 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2484 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation2774_implies_Equation2281 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2281 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2774_implies_Equation2259 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2259 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2774_implies_Equation2462 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2462 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2774_implies_Equation2273 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2774_implies_Equation2285 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2285 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2306_implies_Equation2774 (G : Type*) [Magma G] (h : Equation2306 G) : Equation2774 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ (X4 ◇ X3)) ◇ X4) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1.2.2 in 11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (((X3 ◇ (X1 ◇ (X3 ◇ X4))) ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq21 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq52 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = X1 := superpose eq21 eq9 -- superposition 9,21, 21 into 9, unify on (0).2 in 21 and (0).1.1 in 9
  have eq131 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ (X3 ◇ X0)) ◇ X3) = X3 := superpose eq52 eq13 -- superposition 13,52, 52 into 13, unify on (0).2 in 52 and (0).1.1.1 in 13
  have eq577 : sK0 ≠ sK0 := superpose eq131 eq10 -- superposition 10,131, 131 into 10, unify on (0).2 in 131 and (0).2 in 10
  subsumption eq577 rfl


@[equational_result]
theorem Equation2306_implies_Equation2736 (G : Type*) [Magma G] (h : Equation2306 G) : Equation2736 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ (X4 ◇ X3)) ◇ X4) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1.2.2 in 11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (((X3 ◇ (X1 ◇ (X3 ◇ X4))) ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq21 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq53 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = X1 := superpose eq21 eq9 -- superposition 9,21, 21 into 9, unify on (0).2 in 21 and (0).1.1 in 9
  have eq141 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ (X3 ◇ X0)) ◇ X3) = X3 := superpose eq53 eq13 -- superposition 13,53, 53 into 13, unify on (0).2 in 53 and (0).1.1.1 in 13
  have eq600 : sK0 ≠ sK0 := superpose eq141 eq10 -- superposition 10,141, 141 into 10, unify on (0).2 in 141 and (0).2 in 10
  subsumption eq600 rfl


@[equational_result]
theorem Equation2306_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2306 G) : Equation2644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ X3) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ (X4 ◇ X3)) ◇ X4) = X4 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.1.2.2 in 10
  have eq16 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (((X3 ◇ (X1 ◇ (X3 ◇ X4))) ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq8 eq16 -- forward demodulation 16,8
  have eq52 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = X1 := superpose eq20 eq8 -- superposition 8,20, 20 into 8, unify on (0).2 in 20 and (0).1.1 in 8
  have eq130 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ (X3 ◇ X0)) ◇ X3) = X3 := superpose eq52 eq12 -- superposition 12,52, 52 into 12, unify on (0).2 in 52 and (0).1.1.1 in 12
  have eq576 : sK0 ≠ sK0 := superpose eq130 eq9 -- superposition 9,130, 130 into 9, unify on (0).2 in 130 and (0).2 in 9
  subsumption eq576 rfl


@[equational_result]
theorem Equation2322_implies_Equation2665 (G : Type*) [Magma G] (h : Equation2322 G) : Equation2665 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X4 X5 : G) : ((X4 ◇ (X5 ◇ X1)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2322_implies_Equation2333 (G : Type*) [Magma G] (h : Equation2322 G) : Equation2333 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X1 X4 X5 : G) : ((X4 ◇ (X5 ◇ X1)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq13 (X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq34 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq16 -- superposition 16,13, 13 into 16, unify on (0).2 in 13 and (0).1.1 in 16
  have eq43 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) := superpose eq34 eq10 -- backward demodulation 10,34
  subsumption eq43 eq11


@[equational_result]
theorem Equation2376_implies_Equation2646 (G : Type*) [Magma G] (h : Equation2376 G) : Equation2646 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 X5 : G) : ((X5 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2376_implies_Equation2322 (G : Type*) [Magma G] (h : Equation2376 G) : Equation2322 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 X5 : G) : ((X5 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2376_implies_Equation2782 (G : Type*) [Magma G] (h : Equation2376 G) : Equation2782 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK0 ◇ sK3)) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 X5 : G) : ((X5 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2376_implies_Equation3664 (G : Type*) [Magma G] (h : Equation2376 G) : Equation3664 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X2 X3 X5 : G) : ((X5 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq47 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1.2 in 12
  have eq175 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq47 eq16 -- superposition 16,47, 47 into 16, unify on (0).2 in 47 and (0).1.1 in 16
  have eq256 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq175 eq10 -- superposition 10,175, 175 into 10, unify on (0).2 in 175 and (0).2 in 10
  subsumption eq256 rfl


@[equational_result]
theorem Equation2376_implies_Equation2662 (G : Type*) [Magma G] (h : Equation2376 G) : Equation2662 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 X5 : G) : ((X5 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2376_implies_Equation2702 (G : Type*) [Magma G] (h : Equation2376 G) : Equation2702 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 X5 : G) : ((X5 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2333_implies_Equation2290 (G : Type*) [Magma G] (h : Equation2333 G) : Equation2290 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ (X1 ◇ X2)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq15 eq9 -- backward demodulation 9,15
  have eq21 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq21 eq20


@[equational_result]
theorem Equation2333_implies_Equation2376 (G : Type*) [Magma G] (h : Equation2333 G) : Equation2376 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK3))) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ (X1 ◇ X2)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.2.2 in 9
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq15 eq9 -- backward demodulation 9,15
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq15 eq16 -- forward demodulation 16,15
  have eq58 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = X1 := superpose eq20 eq22 -- superposition 22,20, 20 into 22, unify on (0).2 in 20 and (0).1 in 22
  have eq109 : sK0 ≠ sK0 := superpose eq58 eq10 -- superposition 10,58, 58 into 10, unify on (0).2 in 58 and (0).2 in 10
  subsumption eq109 rfl


@[equational_result]
theorem Equation2333_implies_Equation2778 (G : Type*) [Magma G] (h : Equation2333 G) : Equation2778 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK0 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ (X1 ◇ X2)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq15 eq9 -- backward demodulation 9,15
  have eq28 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq28 rfl


@[equational_result]
theorem Equation2333_implies_Equation2296 (G : Type*) [Magma G] (h : Equation2333 G) : Equation2296 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ (X1 ◇ X2)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq15 eq9 -- backward demodulation 9,15
  have eq21 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq21 eq20


@[equational_result]
theorem Equation2333_implies_Equation2699 (G : Type*) [Magma G] (h : Equation2333 G) : Equation2699 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ (X1 ◇ X2)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.2.2 in 9
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq15 eq16 -- forward demodulation 16,15
  have eq23 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq22 eq10 -- backward demodulation 10,22
  subsumption eq23 eq13


@[equational_result]
theorem Equation2333_implies_Equation2739 (G : Type*) [Magma G] (h : Equation2333 G) : Equation2739 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ (X1 ◇ X2)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq15 eq9 -- backward demodulation 9,15
  have eq27 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq27 rfl


@[equational_result]
theorem Equation2782_implies_Equation3759 (G : Type*) [Magma G] (h : Equation2782 G) : Equation3759 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X2 X4 X5 : G) : ((X2 ◇ (X4 ◇ X5)) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.1.2 in 11
  have eq92 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq20 eq13 -- superposition 13,20, 20 into 13, unify on (0).2 in 20 and (0).1.1 in 13
  have eq231 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq92 eq10 -- superposition 10,92, 92 into 10, unify on (0).2 in 92 and (0).2 in 10
  subsumption eq231 rfl


@[equational_result]
theorem Equation2782_implies_Equation2310 (G : Type*) [Magma G] (h : Equation2782 G) : Equation2310 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X2 X4 X5 : G) : ((X2 ◇ (X4 ◇ X5)) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation2782_implies_Equation2364 (G : Type*) [Magma G] (h : Equation2782 G) : Equation2364 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X2 X4 X5 : G) : ((X2 ◇ (X4 ◇ X5)) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.1.2 in 11
  have eq81 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = X1 := superpose eq11 eq20 -- superposition 20,11, 11 into 20, unify on (0).2 in 11 and (0).1 in 20
  have eq158 : sK0 ≠ sK0 := superpose eq81 eq10 -- superposition 10,81, 81 into 10, unify on (0).2 in 81 and (0).2 in 10
  subsumption eq158 rfl


@[equational_result]
theorem Equation2782_implies_Equation2318 (G : Type*) [Magma G] (h : Equation2782 G) : Equation2318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X2 X4 X5 : G) : ((X2 ◇ (X4 ◇ X5)) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation2782_implies_Equation2314 (G : Type*) [Magma G] (h : Equation2782 G) : Equation2314 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X2 X4 X5 : G) : ((X2 ◇ (X4 ◇ X5)) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation2782_implies_Equation2306 (G : Type*) [Magma G] (h : Equation2782 G) : Equation2306 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X2 X4 X5 : G) : ((X2 ◇ (X4 ◇ X5)) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation2782_implies_Equation3712 (G : Type*) [Magma G] (h : Equation2782 G) : Equation3712 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X2 X4 X5 : G) : ((X2 ◇ (X4 ◇ X5)) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.1.2 in 11
  have eq83 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq83 rfl


@[equational_result]
theorem Equation2782_implies_Equation224 (G : Type*) [Magma G] (h : Equation2782 G) : Equation224 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X4 X5 : G) : ((X2 ◇ (X4 ◇ X5)) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation2782_implies_Equation2333 (G : Type*) [Magma G] (h : Equation2782 G) : Equation2333 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X2 X4 X5 : G) : ((X2 ◇ (X4 ◇ X5)) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq19 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq19 eq11


@[equational_result]
theorem Equation2782_implies_Equation2368 (G : Type*) [Magma G] (h : Equation2782 G) : Equation2368 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X2 X4 X5 : G) : ((X2 ◇ (X4 ◇ X5)) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.1.2 in 11
  have eq81 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = X1 := superpose eq11 eq20 -- superposition 20,11, 11 into 20, unify on (0).2 in 11 and (0).1 in 20
  have eq158 : sK0 ≠ sK0 := superpose eq81 eq10 -- superposition 10,81, 81 into 10, unify on (0).2 in 81 and (0).2 in 10
  subsumption eq158 rfl


@[equational_result]
theorem Equation2923_implies_Equation2628 (G : Type*) [Magma G] (h : Equation2923 G) : Equation2628 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK3) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = (((X3 ◇ X1) ◇ X3) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = ((X1 ◇ ((X3 ◇ (X1 ◇ X4)) ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1 in 12
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X3 ◇ X1) ◇ X3)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2.1.2 in 12
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ X5)) ◇ X4) = ((((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X4 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ X5)) ◇ X4)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1.1 in 11
  have eq24 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X2)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1 in 11
  have eq25 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X1) ◇ X3) = (((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X4) ◇ ((X3 ◇ X1) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq27 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X2)) ◇ X4) = (((X5 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X5) ◇ ((X4 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X2)) ◇ X4)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq30 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) = (((X4 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X4) ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq34 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ ((X4 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X2)) ◇ X4)) ◇ (X0 ◇ X1)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.2.1.2 in 12
  have eq35 (X0 X1 X2 X3 : G) : (((X2 ◇ (X1 ◇ X3)) ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) ◇ X2) = X2 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.2.1 in 12
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ X0) = ((((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ ((X4 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ X5)) ◇ X4)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1 in 12
  have eq52 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X1) ◇ X4) = ((((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X4 ◇ X1) ◇ X4)) := superpose eq11 eq25 -- superposition 25,11, 11 into 25, unify on (0).2 in 11 and (0).2.1.1 in 25
  have eq134 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ ((X5 ◇ ((X3 ◇ (X0 ◇ X4)) ◇ X3)) ◇ X5)) ◇ X0) = X0 := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).1.1.2.1.2 in 12
  have eq136 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ X0) ◇ X5) = ((((X3 ◇ (X0 ◇ X4)) ◇ X3) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1))) ◇ ((X5 ◇ X0) ◇ X5)) := superpose eq13 eq25 -- superposition 25,13, 13 into 25, unify on (0).2 in 13 and (0).2.1.1 in 25
  have eq278 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X1) = ((((X4 ◇ X1) ◇ X4) ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X4 ◇ X1)) := superpose eq11 eq34 -- superposition 34,11, 11 into 34, unify on (0).2 in 11 and (0).2.1.2.1 in 34
  have eq782 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X4 ◇ (X1 ◇ X5)) ◇ X4)) ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq11 eq134 -- superposition 134,11, 11 into 134, unify on (0).2 in 11 and (0).1.1.2.1 in 134
  have eq1456 (X1 X2 X3 X4 : G) : (X4 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) = ((((X4 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X4) ◇ ((X3 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X3)) ◇ (X4 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1))) := superpose eq27 eq278 -- superposition 278,27, 27 into 278, unify on (0).2 in 27 and (0).2.1.2 in 278
  have eq1457 (X1 X2 X3 X4 : G) : ((X4 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X4) = (((X3 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X3) ◇ ((X4 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X4)) := superpose eq27 eq52 -- superposition 52,27, 27 into 52, unify on (0).2 in 27 and (0).2.1 in 52
  have eq1459 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X1 ◇ (X1 ◇ X2)))) ◇ ((X3 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X3)) ◇ X0) = X0 := superpose eq27 eq35 -- superposition 35,27, 27 into 35, unify on (0).2 in 27 and (0).1.1.2 in 35
  have eq1541 (X1 X2 X3 X4 : G) : (X4 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) = (((X3 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X3) ◇ (X4 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1))) := superpose eq1457 eq1456 -- backward demodulation 1456,1457
  have eq1617 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = (((((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ X3)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq15 eq37 -- superposition 37,15, 15 into 37, unify on (0).2 in 15 and (0).2.1.2.1.2 in 37
  have eq1618 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ X3) = ((((((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0)) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0)) ◇ X4)) ◇ ((X3 ◇ X0) ◇ X3)) := superpose eq34 eq37 -- superposition 37,34, 34 into 37, unify on (0).2 in 34 and (0).2.1.2.1.2 in 37
  have eq1713 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = (((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ X3) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq11 eq1617 -- forward demodulation 1617,11
  have eq1715 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ X3) = (((X4 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0)) ◇ X4) ◇ ((X3 ◇ X0) ◇ X3)) := superpose eq11 eq1618 -- forward demodulation 1618,11
  have eq1900 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = ((((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq24 eq1715 -- superposition 1715,24, 24 into 1715, unify on (0).2 in 24 and (0).2.1.1 in 1715
  have eq1911 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X1) = ((((X4 ◇ X1) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X2)) ◇ X1)) ◇ X0)) ◇ (X4 ◇ X1)) := superpose eq1715 eq9 -- superposition 9,1715, 1715 into 9, unify on (0).2 in 1715 and (0).1.1.1 in 9
  have eq2388 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X5 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ ((X4 ◇ X2) ◇ X4))) ◇ X5) = ((((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) ◇ ((X6 ◇ X1) ◇ X6)) ◇ ((X5 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ ((X4 ◇ X2) ◇ X4))) ◇ X5)) := superpose eq30 eq23 -- superposition 23,30, 30 into 23, unify on (0).2 in 30 and (0).1.1.2 in 23
  have eq2714 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X1) ◇ X4) = ((((X3 ◇ (X1 ◇ X2)) ◇ X3) ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X2))) ◇ X0)) ◇ ((X4 ◇ X1) ◇ X4)) := superpose eq1713 eq25 -- superposition 25,1713, 1713 into 25, unify on (0).2 in 1713 and (0).2.1.1 in 25
  have eq2792 (X0 X1 X2 : G) : (X2 ◇ X0) = ((((X2 ◇ X0) ◇ X2) ◇ (((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) ◇ (X2 ◇ X0)) := superpose eq24 eq1911 -- superposition 1911,24, 24 into 1911, unify on (0).2 in 24 and (0).2.1.2.1 in 1911
  have eq2878 (X0 X1 X2 X3 : G) : (((X3 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X1 ◇ (X1 ◇ X2)))) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ X3) = X3 := superpose eq11 eq1459 -- superposition 1459,11, 11 into 1459, unify on (0).2 in 11 and (0).1.1.2.1 in 1459
  have eq2937 (X2 X3 X5 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X2) = (((X5 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X2)) ◇ X5) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X2)) := superpose eq25 eq1541 -- superposition 1541,25, 25 into 1541, unify on (0).2 in 25 and (0).1 in 1541
  have eq2943 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X2)) ◇ X0) = X0 := superpose eq1541 eq9 -- superposition 9,1541, 1541 into 9, unify on (0).2 in 1541 and (0).1.1 in 9
  have eq3047 (X0 X1 X2 : G) : (X2 ◇ X0) = ((((X2 ◇ X0) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq2937 eq2792 -- backward demodulation 2792,2937
  have eq3049 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq2937 eq1900 -- backward demodulation 1900,2937
  have eq3051 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X2 ◇ X0)) := superpose eq11 eq3047 -- forward demodulation 3047,11
  have eq3059 (X0 X1 X2 X3 : G) : (((X3 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X1 ◇ (X1 ◇ X2)))) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = X3 := superpose eq3049 eq2878 -- backward demodulation 2878,3049
  have eq3178 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq3051 eq2943 -- superposition 2943,3051, 3051 into 2943, unify on (0).2 in 3051 and (0).1.1 in 2943
  have eq3190 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X3) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X4 ◇ X0) ◇ X4)) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X3)) := superpose eq3051 eq23 -- superposition 23,3051, 3051 into 23, unify on (0).2 in 3051 and (0).1.1.2 in 23
  have eq3279 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = X3 := superpose eq3178 eq3059 -- backward demodulation 3059,3178
  have eq3280 (X0 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X3) = (((X4 ◇ X0) ◇ X4) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X3)) := superpose eq3049 eq3190 -- forward demodulation 3190,3049
  have eq3288 (X0 X1 X2 X4 : G) : ((X4 ◇ X1) ◇ X4) = (((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X2))) ◇ X0) ◇ ((X4 ◇ X1) ◇ X4)) := superpose eq3280 eq2714 -- backward demodulation 2714,3280
  have eq3370 (X0 X1 X3 : G) : ((X3 ◇ X1) ◇ X3) = (((X0 ◇ X1) ◇ X0) ◇ ((X3 ◇ X1) ◇ X3)) := superpose eq3279 eq52 -- superposition 52,3279, 3279 into 52, unify on (0).2 in 3279 and (0).2.1 in 52
  have eq3371 (X0 X1 X3 : G) : (X3 ◇ X1) = ((((X3 ◇ X1) ◇ X3) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X3 ◇ X1)) := superpose eq3279 eq278 -- superposition 278,3279, 3279 into 278, unify on (0).2 in 3279 and (0).2.1.2 in 278
  have eq3383 (X0 X1 X3 : G) : (X3 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ X1)) := superpose eq3370 eq3371 -- forward demodulation 3371,3370
  have eq3406 (X0 X1 X2 X4 : G) : ((X4 ◇ X1) ◇ X4) = (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X4 ◇ X1) ◇ X4)) := superpose eq3383 eq3288 -- backward demodulation 3288,3383
  have eq3514 (X0 X1 X4 X5 : G) : (((X1 ◇ ((X4 ◇ (X1 ◇ X5)) ◇ X4)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq3406 eq782 -- backward demodulation 782,3406
  have eq3622 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X5 ◇ ((X4 ◇ X2) ◇ X4)) ◇ X5) = ((((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) ◇ ((X6 ◇ X1) ◇ X6)) ◇ ((X5 ◇ ((X4 ◇ X2) ◇ X4)) ◇ X5)) := superpose eq3406 eq2388 -- backward demodulation 2388,3406
  have eq3778 (X1 X2 X4 X5 X6 : G) : ((X5 ◇ ((X4 ◇ X2) ◇ X4)) ◇ X5) = (((X6 ◇ X1) ◇ X6) ◇ ((X5 ◇ ((X4 ◇ X2) ◇ X4)) ◇ X5)) := superpose eq3406 eq3622 -- forward demodulation 3622,3406
  have eq3781 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (((X4 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X2)) ◇ X4) ◇ (X0 ◇ X1)) := superpose eq3778 eq34 -- backward demodulation 34,3778
  have eq4610 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X0 := superpose eq3383 eq9 -- superposition 9,3383, 3383 into 9, unify on (0).2 in 3383 and (0).1.1 in 9
  have eq4765 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X4 ◇ X2)) := superpose eq3383 eq3781 -- superposition 3781,3383, 3383 into 3781, unify on (0).2 in 3383 and (0).2.1.1 in 3781
  have eq4974 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq4610 -- superposition 4610,12, 12 into 4610, unify on (0).2 in 12 and (0).1.1 in 4610
  have eq5059 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq4974 eq3049 -- backward demodulation 3049,4974
  have eq5128 (X0 X1 X2 X4 : G) : (X4 ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ (X4 ◇ X2)) := superpose eq5059 eq4765 -- backward demodulation 4765,5059
  have eq5132 (X0 X1 X2 X5 : G) : ((X5 ◇ X0) ◇ X5) = ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ ((X5 ◇ X0) ◇ X5)) := superpose eq5128 eq136 -- backward demodulation 136,5128
  have eq5633 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = X1 := superpose eq5132 eq3514 -- backward demodulation 3514,5132
  have eq5953 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq3383 eq5633 -- superposition 5633,3383, 3383 into 5633, unify on (0).2 in 3383 and (0).1.1 in 5633
  have eq6003 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq5953 eq9 -- backward demodulation 9,5953
  have eq6802 : sK0 ≠ ((sK1 ◇ sK2) ◇ sK0) := superpose eq5953 eq10 -- backward demodulation 10,5953
  subsumption eq6802 eq6003


@[equational_result]
theorem Equation2915_implies_Equation796 (G : Type*) [Magma G] (h : Equation2915 G) : Equation796 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK3 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK1 ◇ sK0) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation2915_implies_Equation2633 (G : Type*) [Magma G] (h : Equation2915 G) : Equation2633 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK3) ◇ sK3)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK1 ◇ sK3) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation2960_implies_Equation3728 (G : Type*) [Magma G] (h : Equation2960 G) : Equation3728 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq21 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq29 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq21 eq9 -- backward demodulation 9,21
  have eq35 : sK1 ≠ (sK1 ◇ (sK2 ◇ sK1)) := superpose eq29 eq10 -- backward demodulation 10,29
  have eq36 : sK1 ≠ (sK1 ◇ sK1) := superpose eq29 eq35 -- forward demodulation 35,29
  subsumption eq36 eq29


