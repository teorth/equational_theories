import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation2998_implies_Equation4622 (G : Type*) [Magma G] (h : Equation2998 G) : Equation4622 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq35 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq46 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq9 eq35 -- forward demodulation 35,9
  have eq59 : sK1 ≠ ((sK2 ◇ sK2) ◇ sK1) := superpose eq46 eq10 -- backward demodulation 10,46
  subsumption eq59 eq46


@[equational_result]
theorem Equation2998_implies_Equation3152 (G : Type*) [Magma G] (h : Equation2998 G) : Equation3152 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq35 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq46 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq9 eq35 -- forward demodulation 35,9
  have eq59 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq46 eq10 -- backward demodulation 10,46
  subsumption eq59 eq46


@[equational_result]
theorem Equation2998_implies_Equation3139 (G : Type*) [Magma G] (h : Equation2998 G) : Equation3139 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq35 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq46 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq9 eq35 -- forward demodulation 35,9
  have eq59 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq46 eq10 -- backward demodulation 10,46
  subsumption eq59 eq46


@[equational_result]
theorem Equation2998_implies_Equation4065 (G : Type*) [Magma G] (h : Equation2998 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) ◇ X3) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq34 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0)) ◇ X3) = X3 := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1.1 in 11
  have eq45 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq8 eq34 -- forward demodulation 34,8
  have eq58 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq45 eq9 -- backward demodulation 9,45
  subsumption eq58 rfl


@[equational_result]
theorem Equation2998_implies_Equation3050 (G : Type*) [Magma G] (h : Equation2998 G) : Equation3050 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) ◇ X3) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq34 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0)) ◇ X3) = X3 := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1.1 in 11
  have eq45 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq8 eq34 -- forward demodulation 34,8
  have eq58 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq45 eq9 -- backward demodulation 9,45
  subsumption eq58 eq45


@[equational_result]
theorem Equation2998_implies_Equation4118 (G : Type*) [Magma G] (h : Equation2998 G) : Equation4118 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq35 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq46 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq9 eq35 -- forward demodulation 35,9
  have eq59 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq46 eq10 -- backward demodulation 10,46
  subsumption eq59 rfl


@[equational_result]
theorem Equation2998_implies_Equation2902 (G : Type*) [Magma G] (h : Equation2998 G) : Equation2902 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq31 (X0 X1 X2 X3 : G) : (((X2 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X2) ◇ X3) = X3 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1.2 in 12
  have eq35 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq46 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq9 eq35 -- forward demodulation 35,9
  have eq57 (X1 X2 X3 : G) : (((X2 ◇ (X1 ◇ X1)) ◇ X2) ◇ X3) = X3 := superpose eq46 eq31 -- backward demodulation 31,46
  have eq96 : sK0 ≠ sK0 := superpose eq57 eq10 -- superposition 10,57, 57 into 10, unify on (0).2 in 57 and (0).2 in 10
  subsumption eq96 rfl


@[equational_result]
theorem Equation2998_implies_Equation2872 (G : Type*) [Magma G] (h : Equation2998 G) : Equation2872 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq31 (X0 X1 X2 X3 : G) : (((X2 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X2) ◇ X3) = X3 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1.2 in 12
  have eq35 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq46 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq9 eq35 -- forward demodulation 35,9
  have eq57 (X1 X2 X3 : G) : (((X2 ◇ (X1 ◇ X1)) ◇ X2) ◇ X3) = X3 := superpose eq46 eq31 -- backward demodulation 31,46
  have eq96 : sK0 ≠ sK0 := superpose eq57 eq10 -- superposition 10,57, 57 into 10, unify on (0).2 in 57 and (0).2 in 10
  subsumption eq96 rfl


@[equational_result]
theorem Equation2998_implies_Equation3011 (G : Type*) [Magma G] (h : Equation2998 G) : Equation3011 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq31 (X0 X1 X2 X3 : G) : (((X2 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X2) ◇ X3) = X3 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1.2 in 12
  have eq35 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq46 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq9 eq35 -- forward demodulation 35,9
  have eq57 (X1 X2 X3 : G) : (((X2 ◇ (X1 ◇ X1)) ◇ X2) ◇ X3) = X3 := superpose eq46 eq31 -- backward demodulation 31,46
  have eq96 : sK0 ≠ sK0 := superpose eq57 eq10 -- superposition 10,57, 57 into 10, unify on (0).2 in 57 and (0).2 in 10
  subsumption eq96 rfl


@[equational_result]
theorem Equation690_implies_Equation4606 (G : Type*) [Magma G] (h : Equation690 G) : Equation4606 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2)) = (X1 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X1 X3 X4 : G) : ((X3 ◇ (X1 ◇ X3)) ◇ (X4 ◇ (X3 ◇ X4))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2.1 in 11
  have eq15 (X0 X3 X4 : G) : (((X3 ◇ (X0 ◇ X3)) ◇ X3) ◇ (X4 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X4))) = X4 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq21 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X3)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.2 in 9
  have eq27 (X0 X3 X4 : G) : (X4 ◇ (X3 ◇ X4)) = ((X0 ◇ X3) ◇ ((X4 ◇ (X3 ◇ X4)) ◇ X4)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1 in 12
  have eq29 (X0 X3 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ X3) = (X0 ◇ (((X3 ◇ (X0 ◇ X3)) ◇ X3) ◇ (X3 ◇ (X0 ◇ X3)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq37 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq94 (X1 X2 X3 X4 : G) : (X3 ◇ ((X4 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) = (((X2 ◇ (X1 ◇ X2)) ◇ X2) ◇ ((X3 ◇ ((X4 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) ◇ X3)) := superpose eq27 eq12 -- superposition 12,27, 27 into 12, unify on (0).2 in 27 and (0).1.2.1.2 in 12
  have eq115 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).1.2 in 15
  have eq126 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).1.2 in 13
  have eq139 (X0 X3 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ X3) = (X0 ◇ ((X0 ◇ X3) ◇ (X3 ◇ (X0 ◇ X3)))) := superpose eq115 eq29 -- backward demodulation 29,115
  have eq334 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X2 ◇ X3)) := superpose eq37 eq9 -- superposition 9,37, 37 into 9, unify on (0).2 in 37 and (0).1.2 in 9
  have eq410 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X0)) = (((X3 ◇ X4) ◇ X1) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq126 eq21 -- superposition 21,126, 126 into 21, unify on (0).2 in 126 and (0).2.2 in 21
  have eq412 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq126 eq27 -- superposition 27,126, 126 into 27, unify on (0).2 in 126 and (0).2.2 in 27
  have eq493 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (X3 ◇ ((X4 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) := superpose eq410 eq94 -- backward demodulation 94,410
  have eq549 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) = ((X2 ◇ X0) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq139 eq27 -- superposition 27,139, 139 into 27, unify on (0).2 in 139 and (0).1.2 in 27
  have eq589 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) = ((X2 ◇ X0) ◇ ((X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq412 eq549 -- forward demodulation 549,412
  have eq590 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq11 eq589 -- forward demodulation 589,11
  have eq1633 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ (X3 ◇ (X0 ◇ X3))) = ((X4 ◇ X3) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq11 eq334 -- superposition 334,11, 11 into 334, unify on (0).2 in 11 and (0).2.1.2 in 334
  have eq2738 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) = ((X0 ◇ ((X4 ◇ X5) ◇ X0)) ◇ (((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) ◇ (X0 ◇ (X2 ◇ X0)))) := superpose eq493 eq11 -- superposition 11,493, 493 into 11, unify on (0).2 in 493 and (0).1.2.2 in 11
  have eq2858 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) = ((X0 ◇ ((X4 ◇ X5) ◇ X0)) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0)))) := superpose eq1633 eq2738 -- forward demodulation 2738,1633
  have eq2859 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) := superpose eq11 eq2858 -- forward demodulation 2858,11
  have eq4970 (X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X3) = ((X4 ◇ ((X1 ◇ X2) ◇ (X2 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2)))) ◇ X3) := superpose eq590 eq2859 -- superposition 2859,590, 590 into 2859, unify on (0).2 in 590 and (0).2.1.2.2 in 2859
  have eq5181 (X1 X2 X3 X4 : G) : ((X4 ◇ X2) ◇ X3) = ((X1 ◇ X2) ◇ X3) := superpose eq9 eq4970 -- forward demodulation 4970,9
  have eq5379 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq5181 eq10 -- superposition 10,5181, 5181 into 10, unify on (0).2 in 5181 and (0).2 in 10
  subsumption eq5379 eq5181


@[equational_result]
theorem Equation690_implies_Equation4689 (G : Type*) [Magma G] (h : Equation690 G) : Equation4689 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK3 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2)) = (X1 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X1 X3 X4 : G) : ((X3 ◇ (X1 ◇ X3)) ◇ (X4 ◇ (X3 ◇ X4))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2.1 in 11
  have eq15 (X0 X3 X4 : G) : (((X3 ◇ (X0 ◇ X3)) ◇ X3) ◇ (X4 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X4))) = X4 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq21 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X3)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.2 in 9
  have eq27 (X0 X3 X4 : G) : (X4 ◇ (X3 ◇ X4)) = ((X0 ◇ X3) ◇ ((X4 ◇ (X3 ◇ X4)) ◇ X4)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1 in 12
  have eq29 (X0 X3 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ X3) = (X0 ◇ (((X3 ◇ (X0 ◇ X3)) ◇ X3) ◇ (X3 ◇ (X0 ◇ X3)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq37 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq94 (X1 X2 X3 X4 : G) : (X3 ◇ ((X4 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) = (((X2 ◇ (X1 ◇ X2)) ◇ X2) ◇ ((X3 ◇ ((X4 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) ◇ X3)) := superpose eq27 eq12 -- superposition 12,27, 27 into 12, unify on (0).2 in 27 and (0).1.2.1.2 in 12
  have eq115 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).1.2 in 15
  have eq126 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).1.2 in 13
  have eq139 (X0 X3 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ X3) = (X0 ◇ ((X0 ◇ X3) ◇ (X3 ◇ (X0 ◇ X3)))) := superpose eq115 eq29 -- backward demodulation 29,115
  have eq334 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X2 ◇ X3)) := superpose eq37 eq9 -- superposition 9,37, 37 into 9, unify on (0).2 in 37 and (0).1.2 in 9
  have eq410 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X0)) = (((X3 ◇ X4) ◇ X1) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq126 eq21 -- superposition 21,126, 126 into 21, unify on (0).2 in 126 and (0).2.2 in 21
  have eq412 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq126 eq27 -- superposition 27,126, 126 into 27, unify on (0).2 in 126 and (0).2.2 in 27
  have eq493 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (X3 ◇ ((X4 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) := superpose eq410 eq94 -- backward demodulation 94,410
  have eq549 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) = ((X2 ◇ X0) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq139 eq27 -- superposition 27,139, 139 into 27, unify on (0).2 in 139 and (0).1.2 in 27
  have eq589 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) = ((X2 ◇ X0) ◇ ((X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq412 eq549 -- forward demodulation 549,412
  have eq590 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq11 eq589 -- forward demodulation 589,11
  have eq1633 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ (X3 ◇ (X0 ◇ X3))) = ((X4 ◇ X3) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq11 eq334 -- superposition 334,11, 11 into 334, unify on (0).2 in 11 and (0).2.1.2 in 334
  have eq2738 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) = ((X0 ◇ ((X4 ◇ X5) ◇ X0)) ◇ (((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) ◇ (X0 ◇ (X2 ◇ X0)))) := superpose eq493 eq11 -- superposition 11,493, 493 into 11, unify on (0).2 in 493 and (0).1.2.2 in 11
  have eq2858 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) = ((X0 ◇ ((X4 ◇ X5) ◇ X0)) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0)))) := superpose eq1633 eq2738 -- forward demodulation 2738,1633
  have eq2859 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) := superpose eq11 eq2858 -- forward demodulation 2858,11
  have eq4970 (X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X3) = ((X4 ◇ ((X1 ◇ X2) ◇ (X2 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2)))) ◇ X3) := superpose eq590 eq2859 -- superposition 2859,590, 590 into 2859, unify on (0).2 in 590 and (0).2.1.2.2 in 2859
  have eq5181 (X1 X2 X3 X4 : G) : ((X4 ◇ X2) ◇ X3) = ((X1 ◇ X2) ◇ X3) := superpose eq9 eq4970 -- forward demodulation 4970,9
  have eq5379 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ ((X0 ◇ sK1) ◇ sK2) := superpose eq5181 eq10 -- superposition 10,5181, 5181 into 10, unify on (0).2 in 5181 and (0).2 in 10
  subsumption eq5379 eq5181


@[equational_result]
theorem Equation2450_implies_Equation151 (G : Type*) [Magma G] (h : Equation2450 G) : Equation151 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq16 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq20 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1 in 11
  have eq21 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).1.2 in 10
  have eq22 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.2 in 8
  have eq25 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq10 eq16 -- forward demodulation 16,10
  have eq28 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq20 -- forward demodulation 20,8
  have eq29 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) ◇ X0) := superpose eq28 eq25 -- backward demodulation 25,28
  have eq30 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq10 eq21 -- forward demodulation 21,10
  have eq31 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq28 eq30 -- forward demodulation 30,28
  have eq32 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq31 eq29 -- backward demodulation 29,31
  have eq34 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq28 eq22 -- forward demodulation 22,28
  have eq35 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq34 eq32 -- backward demodulation 32,34
  have eq73 : sK0 ≠ sK0 := superpose eq35 eq9 -- superposition 9,35, 35 into 9, unify on (0).2 in 35 and (0).2 in 9
  subsumption eq73 rfl


@[equational_result]
theorem Equation2450_implies_Equation1832 (G : Type*) [Magma G] (h : Equation2450 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq16 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq20 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1 in 11
  have eq21 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).1.2 in 10
  have eq22 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.2 in 8
  have eq25 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq10 eq16 -- forward demodulation 16,10
  have eq28 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq20 -- forward demodulation 20,8
  have eq29 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) ◇ X0) := superpose eq28 eq25 -- backward demodulation 25,28
  have eq30 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq10 eq21 -- forward demodulation 21,10
  have eq31 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq28 eq30 -- forward demodulation 30,28
  have eq32 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq31 eq29 -- backward demodulation 29,31
  have eq34 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq28 eq22 -- forward demodulation 22,28
  have eq35 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq34 eq32 -- backward demodulation 32,34
  have eq74 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq35 eq11 -- superposition 11,35, 35 into 11, unify on (0).2 in 35 and (0).1.1.2.1 in 11
  have eq75 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq35 eq10 -- superposition 10,35, 35 into 10, unify on (0).2 in 35 and (0).1.2.1 in 10
  have eq76 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq35 eq8 -- superposition 8,35, 35 into 8, unify on (0).2 in 35 and (0).1.1.2.1 in 8
  have eq78 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq75 eq74 -- backward demodulation 74,75
  have eq80 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq76 eq78 -- backward demodulation 78,76
  have eq81 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq80 eq75 -- backward demodulation 75,80
  have eq82 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq35 eq81 -- forward demodulation 81,35
  have eq83 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq82 eq76 -- backward demodulation 76,82
  have eq86 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq83 eq9 -- backward demodulation 9,83
  subsumption eq86 eq35


@[equational_result]
theorem Equation2450_implies_Equation203 (G : Type*) [Magma G] (h : Equation2450 G) : Equation203 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq16 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq20 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1 in 11
  have eq21 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).1.2 in 10
  have eq22 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.2 in 8
  have eq25 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq10 eq16 -- forward demodulation 16,10
  have eq28 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq20 -- forward demodulation 20,8
  have eq29 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) ◇ X0) := superpose eq28 eq25 -- backward demodulation 25,28
  have eq30 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq10 eq21 -- forward demodulation 21,10
  have eq31 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq28 eq30 -- forward demodulation 30,28
  have eq32 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq31 eq29 -- backward demodulation 29,31
  have eq34 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq28 eq22 -- forward demodulation 22,28
  have eq35 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq34 eq32 -- backward demodulation 32,34
  have eq74 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq35 eq11 -- superposition 11,35, 35 into 11, unify on (0).2 in 35 and (0).1.1.2.1 in 11
  have eq75 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq35 eq10 -- superposition 10,35, 35 into 10, unify on (0).2 in 35 and (0).1.2.1 in 10
  have eq76 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq35 eq8 -- superposition 8,35, 35 into 8, unify on (0).2 in 35 and (0).1.1.2.1 in 8
  have eq78 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq75 eq74 -- backward demodulation 74,75
  have eq80 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq76 eq78 -- backward demodulation 78,76
  have eq81 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq80 eq75 -- backward demodulation 75,80
  have eq82 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq35 eq81 -- forward demodulation 81,35
  have eq83 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq82 eq76 -- backward demodulation 76,82
  have eq86 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq83 eq9 -- backward demodulation 9,83
  subsumption eq86 eq34


@[equational_result]
theorem Equation2450_implies_Equation3253 (G : Type*) [Magma G] (h : Equation2450 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq16 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq20 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1 in 11
  have eq21 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).1.2 in 10
  have eq22 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.2 in 8
  have eq25 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq10 eq16 -- forward demodulation 16,10
  have eq28 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq20 -- forward demodulation 20,8
  have eq29 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) ◇ X0) := superpose eq28 eq25 -- backward demodulation 25,28
  have eq30 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq10 eq21 -- forward demodulation 21,10
  have eq31 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq28 eq30 -- forward demodulation 30,28
  have eq32 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq31 eq29 -- backward demodulation 29,31
  have eq34 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq28 eq22 -- forward demodulation 22,28
  have eq35 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq34 eq32 -- backward demodulation 32,34
  have eq74 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq35 eq11 -- superposition 11,35, 35 into 11, unify on (0).2 in 35 and (0).1.1.2.1 in 11
  have eq75 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq35 eq10 -- superposition 10,35, 35 into 10, unify on (0).2 in 35 and (0).1.2.1 in 10
  have eq76 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq35 eq8 -- superposition 8,35, 35 into 8, unify on (0).2 in 35 and (0).1.1.2.1 in 8
  have eq78 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq75 eq74 -- backward demodulation 74,75
  have eq80 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq76 eq78 -- backward demodulation 78,76
  have eq81 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq80 eq75 -- backward demodulation 75,80
  have eq82 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq35 eq81 -- forward demodulation 81,35
  have eq83 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq82 eq76 -- backward demodulation 76,82
  have eq86 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq83 eq9 -- backward demodulation 9,83
  subsumption eq86 eq83


@[equational_result]
theorem Equation2450_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2450 G) : Equation2238 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq16 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq20 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1 in 11
  have eq21 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).1.2 in 10
  have eq22 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.2 in 8
  have eq25 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq10 eq16 -- forward demodulation 16,10
  have eq28 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq20 -- forward demodulation 20,8
  have eq29 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) ◇ X0) := superpose eq28 eq25 -- backward demodulation 25,28
  have eq30 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq10 eq21 -- forward demodulation 21,10
  have eq31 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq28 eq30 -- forward demodulation 30,28
  have eq32 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq31 eq29 -- backward demodulation 29,31
  have eq34 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq28 eq22 -- forward demodulation 22,28
  have eq35 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq34 eq32 -- backward demodulation 32,34
  have eq74 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq35 eq11 -- superposition 11,35, 35 into 11, unify on (0).2 in 35 and (0).1.1.2.1 in 11
  have eq75 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq35 eq10 -- superposition 10,35, 35 into 10, unify on (0).2 in 35 and (0).1.2.1 in 10
  have eq76 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq35 eq8 -- superposition 8,35, 35 into 8, unify on (0).2 in 35 and (0).1.1.2.1 in 8
  have eq78 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq75 eq74 -- backward demodulation 74,75
  have eq80 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq76 eq78 -- backward demodulation 78,76
  have eq81 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq80 eq75 -- backward demodulation 75,80
  have eq82 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq35 eq81 -- forward demodulation 81,35
  have eq83 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq82 eq76 -- backward demodulation 76,82
  have eq86 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq83 eq9 -- backward demodulation 9,83
  have eq87 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq83 eq86 -- forward demodulation 86,83
  subsumption eq87 eq34


@[equational_result]
theorem Equation2450_implies_Equation1426 (G : Type*) [Magma G] (h : Equation2450 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq16 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq20 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1 in 11
  have eq21 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).1.2 in 10
  have eq22 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.2 in 8
  have eq25 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq10 eq16 -- forward demodulation 16,10
  have eq28 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq20 -- forward demodulation 20,8
  have eq29 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) ◇ X0) := superpose eq28 eq25 -- backward demodulation 25,28
  have eq30 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq10 eq21 -- forward demodulation 21,10
  have eq31 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq28 eq30 -- forward demodulation 30,28
  have eq32 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq31 eq29 -- backward demodulation 29,31
  have eq34 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq28 eq22 -- forward demodulation 22,28
  have eq35 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq34 eq32 -- backward demodulation 32,34
  have eq74 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq35 eq11 -- superposition 11,35, 35 into 11, unify on (0).2 in 35 and (0).1.1.2.1 in 11
  have eq75 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq35 eq10 -- superposition 10,35, 35 into 10, unify on (0).2 in 35 and (0).1.2.1 in 10
  have eq76 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq35 eq8 -- superposition 8,35, 35 into 8, unify on (0).2 in 35 and (0).1.1.2.1 in 8
  have eq78 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq75 eq74 -- backward demodulation 74,75
  have eq80 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq76 eq78 -- backward demodulation 78,76
  have eq81 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq80 eq75 -- backward demodulation 75,80
  have eq82 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq35 eq81 -- forward demodulation 81,35
  have eq83 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq82 eq76 -- backward demodulation 76,82
  have eq86 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq83 eq9 -- backward demodulation 9,83
  subsumption eq86 eq35


@[equational_result]
theorem Equation2450_implies_Equation307 (G : Type*) [Magma G] (h : Equation2450 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq16 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq20 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1 in 11
  have eq21 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).1.2 in 10
  have eq22 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.2 in 8
  have eq25 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq10 eq16 -- forward demodulation 16,10
  have eq28 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq20 -- forward demodulation 20,8
  have eq29 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) ◇ X0) := superpose eq28 eq25 -- backward demodulation 25,28
  have eq30 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq10 eq21 -- forward demodulation 21,10
  have eq31 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq28 eq30 -- forward demodulation 30,28
  have eq32 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq31 eq29 -- backward demodulation 29,31
  have eq34 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq28 eq22 -- forward demodulation 22,28
  have eq35 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq34 eq32 -- backward demodulation 32,34
  have eq74 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq35 eq11 -- superposition 11,35, 35 into 11, unify on (0).2 in 35 and (0).1.1.2.1 in 11
  have eq75 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq35 eq10 -- superposition 10,35, 35 into 10, unify on (0).2 in 35 and (0).1.2.1 in 10
  have eq76 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq35 eq8 -- superposition 8,35, 35 into 8, unify on (0).2 in 35 and (0).1.1.2.1 in 8
  have eq78 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq75 eq74 -- backward demodulation 74,75
  have eq80 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq76 eq78 -- backward demodulation 78,76
  have eq81 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq80 eq75 -- backward demodulation 75,80
  have eq82 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq35 eq81 -- forward demodulation 81,35
  have eq83 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq82 eq76 -- backward demodulation 76,82
  have eq124 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq83 eq9 -- superposition 9,83, 83 into 9, unify on (0).2 in 83 and (0).2 in 9
  subsumption eq124 rfl


@[equational_result]
theorem Equation246_implies_Equation2406 (G : Type*) [Magma G] (h : Equation246 G) : Equation2406 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation246_implies_Equation2303 (G : Type*) [Magma G] (h : Equation246 G) : Equation2303 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation246_implies_Equation2266 (G : Type*) [Magma G] (h : Equation246 G) : Equation2266 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation246_implies_Equation2281 (G : Type*) [Magma G] (h : Equation246 G) : Equation2281 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation246_implies_Equation2253 (G : Type*) [Magma G] (h : Equation246 G) : Equation2253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation464_implies_Equation4065 (G : Type*) [Magma G] (h : Equation464 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq9 -- backward demodulation 9,12
  subsumption eq13 rfl


@[equational_result]
theorem Equation464_implies_Equation3456 (G : Type*) [Magma G] (h : Equation464 G) : Equation3456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq9 -- backward demodulation 9,12
  subsumption eq13 rfl


@[equational_result]
theorem Equation464_implies_Equation1832 (G : Type*) [Magma G] (h : Equation464 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq15 rfl


@[equational_result]
theorem Equation464_implies_Equation3050 (G : Type*) [Magma G] (h : Equation464 G) : Equation3050 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq12 eq9 -- backward demodulation 9,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation464_implies_Equation23 (G : Type*) [Magma G] (h : Equation464 G) : Equation23 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq14 : sK0 ≠ sK0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq14 rfl


@[equational_result]
theorem Equation464_implies_Equation4118 (G : Type*) [Magma G] (h : Equation464 G) : Equation4118 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 rfl


@[equational_result]
theorem Equation464_implies_Equation3522 (G : Type*) [Magma G] (h : Equation464 G) : Equation3522 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq13 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 rfl


@[equational_result]
theorem Equation1874_implies_Equation2467 (G : Type*) [Magma G] (h : Equation1874 G) : Equation2467 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X4 X5 : G) : ((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X4 X5 : G) : (X4 ◇ X0) = (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq36 (X0 X4 : G) : ((X4 ◇ X0) ◇ X0) = X4 := superpose eq14 eq13 -- backward demodulation 13,14
  have eq42 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X3)) = (X2 ◇ X0) := superpose eq36 eq12 -- superposition 12,36, 36 into 12, unify on (0).2 in 36 and (0).2.2 in 12
  have eq49 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq42 eq10 -- backward demodulation 10,42
  subsumption eq49 eq36


@[equational_result]
theorem Equation1874_implies_Equation1660 (G : Type*) [Magma G] (h : Equation1874 G) : Equation1660 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X4 X5 : G) : ((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X4 X5 : G) : (X4 ◇ X0) = (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq29 (X0 : G) : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  have eq36 (X0 X4 : G) : ((X4 ◇ X0) ◇ X0) = X4 := superpose eq14 eq13 -- backward demodulation 13,14
  have eq52 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq36 eq29 -- superposition 29,36, 36 into 29, unify on (0).2 in 36 and (0).2.2 in 29
  subsumption eq52 eq36


@[equational_result]
theorem Equation1874_implies_Equation2481 (G : Type*) [Magma G] (h : Equation1874 G) : Equation2481 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X4 X5 : G) : ((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X4 X5 : G) : (X4 ◇ X0) = (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq36 (X0 X4 : G) : ((X4 ◇ X0) ◇ X0) = X4 := superpose eq14 eq13 -- backward demodulation 13,14
  have eq42 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X3)) = (X2 ◇ X0) := superpose eq36 eq12 -- superposition 12,36, 36 into 12, unify on (0).2 in 36 and (0).2.2 in 12
  have eq49 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq42 eq10 -- backward demodulation 10,42
  subsumption eq49 eq36


@[equational_result]
theorem Equation1874_implies_Equation3460 (G : Type*) [Magma G] (h : Equation1874 G) : Equation3460 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X4 X5 : G) : ((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X4 X5 : G) : (X4 ◇ X0) = (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  have eq36 (X0 X4 : G) : ((X4 ◇ X0) ◇ X0) = X4 := superpose eq14 eq13 -- backward demodulation 13,14
  have eq52 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq36 eq26 -- superposition 26,36, 36 into 26, unify on (0).2 in 36 and (0).2.2 in 26
  subsumption eq52 rfl


@[equational_result]
theorem Equation1874_implies_Equation1631 (G : Type*) [Magma G] (h : Equation1874 G) : Equation1631 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X4 X5 : G) : ((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X4 X5 : G) : (X4 ◇ X0) = (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq26 (X0 : G) : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  have eq36 (X0 X4 : G) : ((X4 ◇ X0) ◇ X0) = X4 := superpose eq14 eq13 -- backward demodulation 13,14
  have eq52 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq36 eq26 -- superposition 26,36, 36 into 26, unify on (0).2 in 36 and (0).2.2 in 26
  subsumption eq52 eq36


@[equational_result]
theorem Equation1874_implies_Equation2473 (G : Type*) [Magma G] (h : Equation1874 G) : Equation2473 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X4 X5 : G) : ((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X4 X5 : G) : (X4 ◇ X0) = (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq36 (X0 X4 : G) : ((X4 ◇ X0) ◇ X0) = X4 := superpose eq14 eq13 -- backward demodulation 13,14
  have eq42 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X3)) = (X2 ◇ X0) := superpose eq36 eq12 -- superposition 12,36, 36 into 12, unify on (0).2 in 36 and (0).2.2 in 12
  have eq49 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq42 eq10 -- backward demodulation 10,42
  subsumption eq49 eq36


@[equational_result]
theorem Equation1874_implies_Equation4357 (G : Type*) [Magma G] (h : Equation1874 G) : Equation4357 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq30 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq30 eq12


@[equational_result]
theorem Equation1874_implies_Equation1633 (G : Type*) [Magma G] (h : Equation1874 G) : Equation1633 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X4 X5 : G) : ((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X4 X5 : G) : (X4 ◇ X0) = (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq26 (X0 : G) : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  have eq36 (X0 X4 : G) : ((X4 ◇ X0) ◇ X0) = X4 := superpose eq14 eq13 -- backward demodulation 13,14
  have eq52 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq36 eq26 -- superposition 26,36, 36 into 26, unify on (0).2 in 36 and (0).2.2 in 26
  subsumption eq52 eq36


@[equational_result]
theorem Equation1874_implies_Equation2452 (G : Type*) [Magma G] (h : Equation1874 G) : Equation2452 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X4 X5 : G) : ((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X4 X5 : G) : (X4 ◇ X0) = (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq36 (X0 X4 : G) : ((X4 ◇ X0) ◇ X0) = X4 := superpose eq14 eq13 -- backward demodulation 13,14
  have eq42 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X3)) = (X2 ◇ X0) := superpose eq36 eq12 -- superposition 12,36, 36 into 12, unify on (0).2 in 36 and (0).2.2 in 12
  have eq49 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq42 eq10 -- backward demodulation 10,42
  subsumption eq49 eq36


@[equational_result]
theorem Equation4514_implies_Equation4469 (G : Type*) [Magma G] (h : Equation4514 G) : Equation4469 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq36 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK1)) ≠ (sK0 ◇ (X1 ◇ sK0)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1 in 16
  have eq50 (X1 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ (X1 ◇ sK0)) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).1 in 36
  have eq77 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq95 (X0 X1 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (X1 ◇ X0))) := superpose eq9 eq50 -- superposition 50,9, 9 into 50, unify on (0).2 in 9 and (0).2.2 in 50
  subsumption eq95 eq77


@[equational_result]
theorem Equation4514_implies_Equation4361 (G : Type*) [Magma G] (h : Equation4514 G) : Equation4361 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ sK4)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq36 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK4)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  have eq64 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq81 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK2)) ≠ (sK0 ◇ (X1 ◇ sK4)) := superpose eq15 eq36 -- superposition 36,15, 15 into 36, unify on (0).2 in 15 and (0).1 in 36
  have eq153 (X1 : G) : (sK0 ◇ (X1 ◇ sK4)) ≠ ((sK0 ◇ sK2) ◇ sK0) := superpose eq9 eq81 -- superposition 81,9, 9 into 81, unify on (0).2 in 9 and (0).1 in 81
  have eq323 (X0 X1 : G) : ((sK0 ◇ sK2) ◇ sK0) ≠ (sK0 ◇ (sK4 ◇ (X1 ◇ X0))) := superpose eq9 eq153 -- superposition 153,9, 9 into 153, unify on (0).2 in 9 and (0).1.2 in 153
  subsumption eq323 eq64


@[equational_result]
theorem Equation4514_implies_Equation4395 (G : Type*) [Magma G] (h : Equation4514 G) : Equation4395 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq36 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK1)) ≠ (sK0 ◇ (X1 ◇ sK0)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1 in 16
  have eq50 (X1 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ (X1 ◇ sK0)) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).1 in 36
  have eq77 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq95 (X0 X1 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (X1 ◇ X0))) := superpose eq9 eq50 -- superposition 50,9, 9 into 50, unify on (0).2 in 9 and (0).2.2 in 50
  subsumption eq95 eq77


@[equational_result]
theorem Equation4514_implies_Equation4357 (G : Type*) [Magma G] (h : Equation4514 G) : Equation4357 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq36 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK3)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  have eq64 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq81 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK2)) ≠ (sK0 ◇ (X1 ◇ sK3)) := superpose eq15 eq36 -- superposition 36,15, 15 into 36, unify on (0).2 in 15 and (0).1 in 36
  have eq153 (X1 : G) : (sK0 ◇ (X1 ◇ sK3)) ≠ ((sK0 ◇ sK2) ◇ sK0) := superpose eq9 eq81 -- superposition 81,9, 9 into 81, unify on (0).2 in 9 and (0).1 in 81
  have eq323 (X0 X1 : G) : ((sK0 ◇ sK2) ◇ sK0) ≠ (sK0 ◇ (sK3 ◇ (X1 ◇ X0))) := superpose eq9 eq153 -- superposition 153,9, 9 into 153, unify on (0).2 in 9 and (0).1.2 in 153
  subsumption eq323 eq64


@[equational_result]
theorem Equation4514_implies_Equation4282 (G : Type*) [Magma G] (h : Equation4514 G) : Equation4282 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq32 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  have eq64 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq81 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK1)) ≠ (sK0 ◇ (X1 ◇ sK2)) := superpose eq15 eq32 -- superposition 32,15, 15 into 32, unify on (0).2 in 15 and (0).1 in 32
  have eq153 (X1 : G) : (sK0 ◇ (X1 ◇ sK2)) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq9 eq81 -- superposition 81,9, 9 into 81, unify on (0).2 in 9 and (0).1 in 81
  have eq323 (X0 X1 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ (sK2 ◇ (X1 ◇ X0))) := superpose eq9 eq153 -- superposition 153,9, 9 into 153, unify on (0).2 in 9 and (0).1.2 in 153
  subsumption eq323 eq64


@[equational_result]
theorem Equation4514_implies_Equation4475 (G : Type*) [Magma G] (h : Equation4514 G) : Equation4475 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK2) ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).1 in 10
  have eq39 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK1)) ≠ (sK0 ◇ (X1 ◇ sK2)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1 in 16
  have eq50 (X1 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ (X1 ◇ sK2)) := superpose eq9 eq39 -- superposition 39,9, 9 into 39, unify on (0).2 in 9 and (0).1 in 39
  have eq77 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq95 (X0 X1 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ (sK2 ◇ (X1 ◇ X0))) := superpose eq9 eq50 -- superposition 50,9, 9 into 50, unify on (0).2 in 9 and (0).2.2 in 50
  subsumption eq95 eq77


@[equational_result]
theorem Equation4514_implies_Equation4510 (G : Type*) [Magma G] (h : Equation4514 G) : Equation4510 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq39 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK2)) ≠ (sK0 ◇ (X1 ◇ sK1)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1 in 16
  have eq50 (X1 : G) : ((sK0 ◇ sK2) ◇ sK0) ≠ (sK0 ◇ (X1 ◇ sK1)) := superpose eq9 eq39 -- superposition 39,9, 9 into 39, unify on (0).2 in 9 and (0).1 in 39
  have eq77 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq95 (X0 X1 : G) : ((sK0 ◇ sK2) ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (X1 ◇ X0))) := superpose eq9 eq50 -- superposition 50,9, 9 into 50, unify on (0).2 in 9 and (0).2.2 in 50
  subsumption eq95 eq77


@[equational_result]
theorem Equation4514_implies_Equation4358 (G : Type*) [Magma G] (h : Equation4514 G) : Equation4358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq36 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  have eq64 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq81 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK2)) ≠ (sK0 ◇ (X1 ◇ sK1)) := superpose eq15 eq36 -- superposition 36,15, 15 into 36, unify on (0).2 in 15 and (0).1 in 36
  have eq153 (X1 : G) : (sK0 ◇ (X1 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK0) := superpose eq9 eq81 -- superposition 81,9, 9 into 81, unify on (0).2 in 9 and (0).1 in 81
  have eq323 (X0 X1 : G) : ((sK0 ◇ sK2) ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (X1 ◇ X0))) := superpose eq9 eq153 -- superposition 153,9, 9 into 153, unify on (0).2 in 9 and (0).1.2 in 153
  subsumption eq323 eq64


@[equational_result]
theorem Equation4514_implies_Equation4401 (G : Type*) [Magma G] (h : Equation4514 G) : Equation4401 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK2) ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).1 in 10
  have eq35 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK1)) ≠ (sK0 ◇ (X1 ◇ sK2)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1 in 16
  have eq50 (X1 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ (X1 ◇ sK2)) := superpose eq9 eq35 -- superposition 35,9, 9 into 35, unify on (0).2 in 9 and (0).1 in 35
  have eq77 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq95 (X0 X1 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ (sK2 ◇ (X1 ◇ X0))) := superpose eq9 eq50 -- superposition 50,9, 9 into 50, unify on (0).2 in 9 and (0).2.2 in 50
  subsumption eq95 eq77


@[equational_result]
theorem Equation4514_implies_Equation4286 (G : Type*) [Magma G] (h : Equation4514 G) : Equation4286 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq36 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  have eq64 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq81 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK1)) ≠ (sK0 ◇ (X1 ◇ sK0)) := superpose eq15 eq36 -- superposition 36,15, 15 into 36, unify on (0).2 in 15 and (0).1 in 36
  have eq153 (X1 : G) : (sK0 ◇ (X1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq9 eq81 -- superposition 81,9, 9 into 81, unify on (0).2 in 9 and (0).1 in 81
  have eq323 (X0 X1 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (X1 ◇ X0))) := superpose eq9 eq153 -- superposition 153,9, 9 into 153, unify on (0).2 in 9 and (0).1.2 in 153
  subsumption eq323 eq64


@[equational_result]
theorem Equation4514_implies_Equation4288 (G : Type*) [Magma G] (h : Equation4514 G) : Equation4288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq36 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  have eq64 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq81 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK1)) ≠ (sK0 ◇ (X1 ◇ sK2)) := superpose eq15 eq36 -- superposition 36,15, 15 into 36, unify on (0).2 in 15 and (0).1 in 36
  have eq153 (X1 : G) : (sK0 ◇ (X1 ◇ sK2)) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq9 eq81 -- superposition 81,9, 9 into 81, unify on (0).2 in 9 and (0).1 in 81
  have eq323 (X0 X1 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ (sK2 ◇ (X1 ◇ X0))) := superpose eq9 eq153 -- superposition 153,9, 9 into 153, unify on (0).2 in 9 and (0).1.2 in 153
  subsumption eq323 eq64


@[equational_result]
theorem Equation4514_implies_Equation4318 (G : Type*) [Magma G] (h : Equation4514 G) : Equation4318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq36 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  have eq64 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq81 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK0)) ≠ (sK0 ◇ (X1 ◇ sK2)) := superpose eq15 eq36 -- superposition 36,15, 15 into 36, unify on (0).2 in 15 and (0).1 in 36
  have eq153 (X1 : G) : (sK0 ◇ (X1 ◇ sK2)) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq9 eq81 -- superposition 81,9, 9 into 81, unify on (0).2 in 9 and (0).1 in 81
  have eq323 (X0 X1 : G) : ((sK0 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (sK2 ◇ (X1 ◇ X0))) := superpose eq9 eq153 -- superposition 153,9, 9 into 153, unify on (0).2 in 9 and (0).1.2 in 153
  subsumption eq323 eq64


@[equational_result]
theorem Equation4514_implies_Equation4438 (G : Type*) [Magma G] (h : Equation4514 G) : Equation4438 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK2) ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).1 in 10
  have eq39 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK0)) ≠ (sK0 ◇ (X1 ◇ sK2)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1 in 16
  have eq50 (X1 : G) : ((sK0 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (X1 ◇ sK2)) := superpose eq9 eq39 -- superposition 39,9, 9 into 39, unify on (0).2 in 9 and (0).1 in 39
  have eq77 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq95 (X0 X1 : G) : ((sK0 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (sK2 ◇ (X1 ◇ X0))) := superpose eq9 eq50 -- superposition 50,9, 9 into 50, unify on (0).2 in 9 and (0).2.2 in 50
  subsumption eq95 eq77


@[equational_result]
theorem Equation4514_implies_Equation4506 (G : Type*) [Magma G] (h : Equation4514 G) : Equation4506 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq36 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK2)) ≠ (sK0 ◇ (X1 ◇ sK0)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1 in 16
  have eq50 (X1 : G) : ((sK0 ◇ sK2) ◇ sK0) ≠ (sK0 ◇ (X1 ◇ sK0)) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).1 in 36
  have eq77 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq95 (X0 X1 : G) : ((sK0 ◇ sK2) ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (X1 ◇ X0))) := superpose eq9 eq50 -- superposition 50,9, 9 into 50, unify on (0).2 in 9 and (0).2.2 in 50
  subsumption eq95 eq77


@[equational_result]
theorem Equation4514_implies_Equation4518 (G : Type*) [Magma G] (h : Equation4514 G) : Equation4518 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK3) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK3)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq39 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK2)) ≠ (sK0 ◇ (X1 ◇ sK3)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1 in 16
  have eq50 (X1 : G) : ((sK0 ◇ sK2) ◇ sK0) ≠ (sK0 ◇ (X1 ◇ sK3)) := superpose eq9 eq39 -- superposition 39,9, 9 into 39, unify on (0).2 in 9 and (0).1 in 39
  have eq77 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq95 (X0 X1 : G) : ((sK0 ◇ sK2) ◇ sK0) ≠ (sK0 ◇ (sK3 ◇ (X1 ◇ X0))) := superpose eq9 eq50 -- superposition 50,9, 9 into 50, unify on (0).2 in 9 and (0).2.2 in 50
  subsumption eq95 eq77


@[equational_result]
theorem Equation3093_implies_Equation3071 (G : Type*) [Magma G] (h : Equation3093 G) : Equation3071 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (((X0 ◇ X3) ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq47 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X3) = ((((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X4) ◇ X4) ◇ ((X0 ◇ X3) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq205 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq9 eq47 -- superposition 47,9, 9 into 47, unify on (0).2 in 9 and (0).2.1 in 47
  have eq265 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq9 eq205 -- superposition 205,9, 9 into 205, unify on (0).2 in 9 and (0).1 in 205
  have eq402 : sK0 ≠ sK0 := superpose eq265 eq10 -- superposition 10,265, 265 into 10, unify on (0).2 in 265 and (0).2 in 10
  subsumption eq402 rfl


@[equational_result]
theorem Equation3093_implies_Equation3068 (G : Type*) [Magma G] (h : Equation3093 G) : Equation3068 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (((X0 ◇ X3) ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq47 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X3) = ((((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X4) ◇ X4) ◇ ((X0 ◇ X3) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq205 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq9 eq47 -- superposition 47,9, 9 into 47, unify on (0).2 in 9 and (0).2.1 in 47
  have eq265 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq9 eq205 -- superposition 205,9, 9 into 205, unify on (0).2 in 9 and (0).1 in 205
  have eq402 : sK0 ≠ sK0 := superpose eq265 eq10 -- superposition 10,265, 265 into 10, unify on (0).2 in 265 and (0).2 in 10
  subsumption eq402 rfl


@[equational_result]
theorem Equation2296_implies_Equation205 (G : Type*) [Magma G] (h : Equation2296 G) : Equation205 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation4449_implies_Equation4386 (G : Type*) [Magma G] (h : Equation4449 G) : Equation4386 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = (X3 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq41 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq16 eq16 -- superposition 16,16, 16 into 16, unify on (0).2 in 16 and (0).1.2 in 16
  have eq66 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((X0 ◇ sK1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq16 eq17 -- superposition 17,16, 16 into 17, unify on (0).2 in 16 and (0).2.2 in 17
  have eq89 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ X3)) = (((X2 ◇ (X1 ◇ X2)) ◇ X0) ◇ X4) := superpose eq16 eq14 -- superposition 14,16, 16 into 14, unify on (0).2 in 16 and (0).2.1.1 in 14
  have eq3120 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X2 ◇ X4)) = (X5 ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X5)) := superpose eq41 eq89 -- superposition 89,41, 41 into 89, unify on (0).2 in 41 and (0).2 in 89
  have eq3261 (X0 X1 X2 X3 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X3 ◇ ((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X3)) := superpose eq89 eq66 -- superposition 66,89, 89 into 66, unify on (0).2 in 89 and (0).2 in 66
  subsumption eq3261 eq3120


@[equational_result]
theorem Equation4449_implies_Equation4432 (G : Type*) [Magma G] (h : Equation4449 G) : Equation4432 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = (X3 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK0 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq41 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq16 eq16 -- superposition 16,16, 16 into 16, unify on (0).2 in 16 and (0).1.2 in 16
  have eq62 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((X0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq16 eq17 -- superposition 17,16, 16 into 17, unify on (0).2 in 16 and (0).2.2 in 17
  have eq89 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ X3)) = (((X2 ◇ (X1 ◇ X2)) ◇ X0) ◇ X4) := superpose eq16 eq14 -- superposition 14,16, 16 into 14, unify on (0).2 in 16 and (0).2.1.1 in 14
  have eq3120 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X2 ◇ X4)) = (X5 ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X5)) := superpose eq41 eq89 -- superposition 89,41, 41 into 89, unify on (0).2 in 41 and (0).2 in 89
  have eq3303 (X0 X1 X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X3 ◇ ((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X3)) := superpose eq89 eq62 -- superposition 62,89, 89 into 62, unify on (0).2 in 89 and (0).2 in 62
  subsumption eq3303 eq3120


@[equational_result]
theorem Equation4449_implies_Equation4651 (G : Type*) [Magma G] (h : Equation4449 G) : Equation4651 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK2 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = (X3 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq67 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).1.2 in 9
  have eq68 (X0 X1 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ ((X0 ◇ sK2) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq16 eq17 -- superposition 17,16, 16 into 17, unify on (0).2 in 16 and (0).2.2 in 17
  have eq90 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ X3)) = (((X2 ◇ (X1 ◇ X2)) ◇ X0) ◇ X4) := superpose eq16 eq14 -- superposition 14,16, 16 into 14, unify on (0).2 in 16 and (0).2.1.1 in 14
  have eq3120 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X4) ◇ X2) = (X5 ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X5)) := superpose eq67 eq90 -- superposition 90,67, 67 into 90, unify on (0).2 in 67 and (0).2 in 90
  have eq3262 (X0 X1 X2 X3 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (X3 ◇ ((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X3)) := superpose eq90 eq68 -- superposition 68,90, 90 into 68, unify on (0).2 in 90 and (0).2 in 68
  subsumption eq3262 eq3120


@[equational_result]
theorem Equation4449_implies_Equation4454 (G : Type*) [Magma G] (h : Equation4449 G) : Equation4454 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = (X3 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq41 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq16 eq16 -- superposition 16,16, 16 into 16, unify on (0).2 in 16 and (0).1.2 in 16
  have eq66 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((X0 ◇ sK2) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq16 eq17 -- superposition 17,16, 16 into 17, unify on (0).2 in 16 and (0).2.2 in 17
  have eq89 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ X3)) = (((X2 ◇ (X1 ◇ X2)) ◇ X0) ◇ X4) := superpose eq16 eq14 -- superposition 14,16, 16 into 14, unify on (0).2 in 16 and (0).2.1.1 in 14
  have eq3120 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X2 ◇ X4)) = (X5 ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X5)) := superpose eq41 eq89 -- superposition 89,41, 41 into 89, unify on (0).2 in 41 and (0).2 in 89
  have eq3261 (X0 X1 X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X3 ◇ ((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X3)) := superpose eq89 eq66 -- superposition 66,89, 89 into 66, unify on (0).2 in 89 and (0).2 in 66
  subsumption eq3261 eq3120


@[equational_result]
theorem Equation2517_implies_Equation4226 (G : Type*) [Magma G] (h : Equation2517 G) : Equation4226 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK2) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 rfl


@[equational_result]
theorem Equation2517_implies_Equation4622 (G : Type*) [Magma G] (h : Equation2517 G) : Equation4622 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : sK1 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation2517_implies_Equation2652 (G : Type*) [Magma G] (h : Equation2517 G) : Equation2652 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation2517_implies_Equation1746 (G : Type*) [Magma G] (h : Equation2517 G) : Equation1746 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation2517_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2517 G) : Equation2644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq12 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq11


@[equational_result]
theorem Equation2517_implies_Equation1731 (G : Type*) [Magma G] (h : Equation2517 G) : Equation1731 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation2517_implies_Equation2466 (G : Type*) [Magma G] (h : Equation2517 G) : Equation2466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation2517_implies_Equation3139 (G : Type*) [Magma G] (h : Equation2517 G) : Equation3139 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation2517_implies_Equation2687 (G : Type*) [Magma G] (h : Equation2517 G) : Equation2687 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq44 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq44 rfl


@[equational_result]
theorem Equation2517_implies_Equation3759 (G : Type*) [Magma G] (h : Equation2517 G) : Equation3759 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation2517_implies_Equation2746 (G : Type*) [Magma G] (h : Equation2517 G) : Equation2746 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation2517_implies_Equation3659 (G : Type*) [Magma G] (h : Equation2517 G) : Equation3659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq13 rfl


@[equational_result]
theorem Equation2517_implies_Equation2706 (G : Type*) [Magma G] (h : Equation2517 G) : Equation2706 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2517_implies_Equation3712 (G : Type*) [Magma G] (h : Equation2517 G) : Equation3712 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq14 rfl


@[equational_result]
theorem Equation2517_implies_Equation3820 (G : Type*) [Magma G] (h : Equation2517 G) : Equation3820 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq14 rfl


@[equational_result]
theorem Equation2517_implies_Equation3509 (G : Type*) [Magma G] (h : Equation2517 G) : Equation3509 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 rfl


@[equational_result]
theorem Equation2517_implies_Equation3464 (G : Type*) [Magma G] (h : Equation2517 G) : Equation3464 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 rfl


@[equational_result]
theorem Equation2517_implies_Equation3152 (G : Type*) [Magma G] (h : Equation2517 G) : Equation3152 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation2517_implies_Equation3058 (G : Type*) [Magma G] (h : Equation2517 G) : Equation3058 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation2517_implies_Equation2543 (G : Type*) [Magma G] (h : Equation2517 G) : Equation2543 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation2517_implies_Equation3537 (G : Type*) [Magma G] (h : Equation2517 G) : Equation3537 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 rfl


@[equational_result]
theorem Equation2517_implies_Equation2733 (G : Type*) [Magma G] (h : Equation2517 G) : Equation2733 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation2517_implies_Equation2605 (G : Type*) [Magma G] (h : Equation2517 G) : Equation2605 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK2) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation430_implies_Equation8 (G : Type*) [Magma G] (h : Equation430 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq11 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq11 rfl


@[equational_result]
theorem Equation430_implies_Equation3915 (G : Type*) [Magma G] (h : Equation430 G) : Equation3915 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq12 rfl


@[equational_result]
theorem Equation430_implies_Equation1832 (G : Type*) [Magma G] (h : Equation430 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq11 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq10 eq9 -- backward demodulation 9,10
  subsumption eq11 eq10


@[equational_result]
theorem Equation1855_implies_Equation4065 (G : Type*) [Magma G] (h : Equation1855 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X2 ◇ X2) = (((X2 ◇ X2) ◇ X0) ◇ (X3 ◇ X3)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X2)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ (X3 ◇ X3)) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1.2 in 11
  have eq188 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X3 ◇ X3)) = (((X0 ◇ X0) ◇ X1) ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq200 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X0) ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2 in 12
  have eq254 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X2) := superpose eq10 eq188 -- forward demodulation 188,10
  have eq320 (X0 : G) : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ X0) ◇ sK0) := superpose eq200 eq9 -- superposition 9,200, 200 into 9, unify on (0).2 in 200 and (0).2.1 in 9
  subsumption eq320 eq254


@[equational_result]
theorem Equation1855_implies_Equation4069 (G : Type*) [Magma G] (h : Equation1855 G) : Equation4069 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X2) = (((X2 ◇ X2) ◇ X0) ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ (X3 ◇ X3)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq189 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = (((X0 ◇ X0) ◇ X1) ◇ (X3 ◇ X3)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq201 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X0) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq255 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X2) := superpose eq11 eq189 -- forward demodulation 189,11
  have eq299 (X0 : G) : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ X0) ◇ sK2) := superpose eq201 eq10 -- superposition 10,201, 201 into 10, unify on (0).2 in 201 and (0).2.1 in 10
  subsumption eq299 eq255


@[equational_result]
theorem Equation1855_implies_Equation4068 (G : Type*) [Magma G] (h : Equation1855 G) : Equation4068 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X2) = (((X2 ◇ X2) ◇ X0) ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ (X3 ◇ X3)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq189 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X3 ◇ X3)) = (((X0 ◇ X0) ◇ X1) ◇ X2) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq201 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X0) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq255 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X2) := superpose eq11 eq189 -- forward demodulation 189,11
  have eq294 (X0 : G) : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ X0) ◇ sK1) := superpose eq201 eq10 -- superposition 10,201, 201 into 10, unify on (0).2 in 201 and (0).2.1 in 10
  subsumption eq294 eq255


@[equational_result]
theorem Equation4457_implies_Equation4389 (G : Type*) [Magma G] (h : Equation4457 G) : Equation4389 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq61 (X0 X1 : G) : (X1 ◇ (sK1 ◇ X1)) ≠ (X0 ◇ (sK0 ◇ X0)) := superpose eq16 eq17 -- superposition 17,16, 16 into 17, unify on (0).2 in 16 and (0).1 in 17
  have eq114 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1.2 in 16
  have eq158 (X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ X5) = ((X1 ◇ X5) ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq197 (X1 X2 : G) : ((X1 ◇ sK1) ◇ sK1) ≠ (X2 ◇ (sK0 ◇ X2)) := superpose eq9 eq61 -- superposition 61,9, 9 into 61, unify on (0).2 in 9 and (0).1 in 61
  have eq297 (X1 X2 : G) : ((X1 ◇ sK0) ◇ sK0) ≠ ((X2 ◇ sK1) ◇ sK1) := superpose eq9 eq197 -- superposition 197,9, 9 into 197, unify on (0).2 in 9 and (0).2 in 197
  have eq444 (X1 X2 X3 : G) : ((X1 ◇ sK1) ◇ ((X2 ◇ X1) ◇ X1)) ≠ ((X3 ◇ sK0) ◇ sK0) := superpose eq11 eq297 -- superposition 297,11, 11 into 297, unify on (0).2 in 11 and (0).2 in 297
  have eq10949 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq114 eq158 -- superposition 158,114, 114 into 158, unify on (0).2 in 114 and (0).2 in 158
  have eq11050 (X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2)) = (X4 ◇ (X5 ◇ (X4 ◇ X5))) := superpose eq11 eq10949 -- superposition 10949,11, 11 into 10949, unify on (0).2 in 11 and (0).1 in 10949
  have eq11211 (X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) ≠ ((X3 ◇ sK1) ◇ ((X4 ◇ X3) ◇ X3)) := superpose eq10949 eq444 -- superposition 444,10949, 10949 into 444, unify on (0).2 in 10949 and (0).2 in 444
  subsumption eq11211 eq11050


@[equational_result]
theorem Equation4457_implies_Equation4442 (G : Type*) [Magma G] (h : Equation4457 G) : Equation4442 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK0 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq61 (X0 X1 : G) : (X1 ◇ (sK0 ◇ X1)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq16 eq17 -- superposition 17,16, 16 into 17, unify on (0).2 in 16 and (0).1 in 17
  have eq66 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).1.2 in 9
  have eq114 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1.2 in 16
  have eq158 (X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ X5) = ((X1 ◇ X5) ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq197 (X1 X2 : G) : ((X1 ◇ sK0) ◇ sK0) ≠ (X2 ◇ (sK1 ◇ X2)) := superpose eq9 eq61 -- superposition 61,9, 9 into 61, unify on (0).2 in 9 and (0).1 in 61
  have eq291 (X0 X1 X2 : G) : ((X0 ◇ sK1) ◇ (X1 ◇ (X0 ◇ X1))) ≠ ((X2 ◇ sK0) ◇ sK0) := superpose eq16 eq197 -- superposition 197,16, 16 into 197, unify on (0).2 in 16 and (0).2.2 in 197
  have eq11442 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq114 eq158 -- superposition 158,114, 114 into 158, unify on (0).2 in 114 and (0).2 in 158
  have eq11547 (X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ (X3 ◇ (X2 ◇ X3))) = (X4 ◇ (X5 ◇ (X4 ◇ X5))) := superpose eq66 eq11442 -- superposition 11442,66, 66 into 11442, unify on (0).2 in 66 and (0).1 in 11442
  have eq11705 (X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) ≠ ((X3 ◇ sK1) ◇ (X4 ◇ (X3 ◇ X4))) := superpose eq11442 eq291 -- superposition 291,11442, 11442 into 291, unify on (0).2 in 11442 and (0).2 in 291
  subsumption eq11705 eq11547


@[equational_result]
theorem Equation4457_implies_Equation4670 (G : Type*) [Magma G] (h : Equation4457 G) : Equation4670 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK2 ◇ sK3) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = ((X3 ◇ X1) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ (X0 ◇ (sK3 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq37 (X0 X1 : G) : (X1 ◇ (sK3 ◇ X1)) ≠ ((X0 ◇ sK1) ◇ sK1) := superpose eq13 eq17 -- superposition 17,13, 13 into 17, unify on (0).2 in 13 and (0).1 in 17
  have eq115 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1.2 in 16
  have eq164 (X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ X5) = ((X1 ◇ X5) ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq11153 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq115 eq164 -- superposition 164,115, 115 into 164, unify on (0).2 in 115 and (0).2 in 164
  have eq11253 (X1 X2 X3 X4 : G) : (X2 ◇ (X1 ◇ X2)) = (X3 ◇ (X4 ◇ (X3 ◇ X4))) := superpose eq9 eq11153 -- superposition 11153,9, 9 into 11153, unify on (0).2 in 9 and (0).1 in 11153
  have eq11410 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) ≠ (X3 ◇ (sK3 ◇ X3)) := superpose eq11153 eq37 -- superposition 37,11153, 11153 into 37, unify on (0).2 in 11153 and (0).2 in 37
  subsumption eq11410 eq11253


@[equational_result]
theorem Equation4457_implies_Equation4276 (G : Type*) [Magma G] (h : Equation4457 G) : Equation4276 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq13 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = ((X3 ◇ X1) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X0) ◇ X3)) = (((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq20 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X1) = ((X2 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq55 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  have eq67 (X0 X1 : G) : (X0 ◇ (sK0 ◇ X0)) ≠ (X1 ◇ (sK1 ◇ X1)) := superpose eq16 eq55 -- superposition 55,16, 16 into 55, unify on (0).2 in 16 and (0).1 in 55
  have eq120 (X1 X2 : G) : (X2 ◇ (sK1 ◇ X2)) ≠ ((X1 ◇ sK0) ◇ sK0) := superpose eq9 eq67 -- superposition 67,9, 9 into 67, unify on (0).2 in 9 and (0).1 in 67
  have eq287 (X1 X2 : G) : ((X1 ◇ sK1) ◇ sK1) ≠ ((X2 ◇ sK0) ◇ sK0) := superpose eq9 eq120 -- superposition 120,9, 9 into 120, unify on (0).2 in 9 and (0).1 in 120
  have eq355 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2 in 14
  have eq492 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X3)) = (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X1)) := superpose eq20 eq16 -- superposition 16,20, 20 into 16, unify on (0).2 in 20 and (0).1.2 in 16
  have eq10007 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X4 ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq355 eq492 -- superposition 492,355, 355 into 492, unify on (0).2 in 355 and (0).2 in 492
  have eq10687 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X3 ◇ X0) ◇ X2)) = ((X4 ◇ X1) ◇ X1) := superpose eq492 eq10007 -- superposition 10007,492, 492 into 10007, unify on (0).2 in 492 and (0).2 in 10007
  have eq10730 (X1 X2 X3 X4 : G) : ((X4 ◇ sK1) ◇ sK1) ≠ (X1 ◇ ((X2 ◇ (X3 ◇ sK0)) ◇ X1)) := superpose eq10007 eq287 -- superposition 287,10007, 10007 into 287, unify on (0).2 in 10007 and (0).2 in 287
  subsumption eq10730 eq10687


@[equational_result]
theorem Equation4457_implies_Equation4393 (G : Type*) [Magma G] (h : Equation4457 G) : Equation4393 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq61 (X0 X1 : G) : (X1 ◇ (sK2 ◇ X1)) ≠ (X0 ◇ (sK0 ◇ X0)) := superpose eq16 eq17 -- superposition 17,16, 16 into 17, unify on (0).2 in 16 and (0).1 in 17
  have eq114 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1.2 in 16
  have eq158 (X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ X5) = ((X1 ◇ X5) ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq197 (X1 X2 : G) : ((X1 ◇ sK2) ◇ sK2) ≠ (X2 ◇ (sK0 ◇ X2)) := superpose eq9 eq61 -- superposition 61,9, 9 into 61, unify on (0).2 in 9 and (0).1 in 61
  have eq297 (X1 X2 : G) : ((X1 ◇ sK0) ◇ sK0) ≠ ((X2 ◇ sK2) ◇ sK2) := superpose eq9 eq197 -- superposition 197,9, 9 into 197, unify on (0).2 in 9 and (0).2 in 197
  have eq444 (X1 X2 X3 : G) : ((X1 ◇ sK2) ◇ ((X2 ◇ X1) ◇ X1)) ≠ ((X3 ◇ sK0) ◇ sK0) := superpose eq11 eq297 -- superposition 297,11, 11 into 297, unify on (0).2 in 11 and (0).2 in 297
  have eq11442 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq114 eq158 -- superposition 158,114, 114 into 158, unify on (0).2 in 114 and (0).2 in 158
  have eq11543 (X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2)) = (X4 ◇ (X5 ◇ (X4 ◇ X5))) := superpose eq11 eq11442 -- superposition 11442,11, 11 into 11442, unify on (0).2 in 11 and (0).1 in 11442
  have eq11704 (X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) ≠ ((X3 ◇ sK2) ◇ ((X4 ◇ X3) ◇ X3)) := superpose eq11442 eq444 -- superposition 444,11442, 11442 into 444, unify on (0).2 in 11442 and (0).2 in 444
  subsumption eq11704 eq11543


@[equational_result]
theorem Equation4457_implies_Equation4462 (G : Type*) [Magma G] (h : Equation4457 G) : Equation4462 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq61 (X0 X1 : G) : (X1 ◇ (sK2 ◇ X1)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq16 eq17 -- superposition 17,16, 16 into 17, unify on (0).2 in 16 and (0).1 in 17
  have eq114 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1.2 in 16
  have eq158 (X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ X5) = ((X1 ◇ X5) ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq197 (X1 X2 : G) : ((X1 ◇ sK2) ◇ sK2) ≠ (X2 ◇ (sK1 ◇ X2)) := superpose eq9 eq61 -- superposition 61,9, 9 into 61, unify on (0).2 in 9 and (0).1 in 61
  have eq297 (X1 X2 : G) : ((X1 ◇ sK1) ◇ sK1) ≠ ((X2 ◇ sK2) ◇ sK2) := superpose eq9 eq197 -- superposition 197,9, 9 into 197, unify on (0).2 in 9 and (0).2 in 197
  have eq444 (X1 X2 X3 : G) : ((X1 ◇ sK2) ◇ ((X2 ◇ X1) ◇ X1)) ≠ ((X3 ◇ sK1) ◇ sK1) := superpose eq11 eq297 -- superposition 297,11, 11 into 297, unify on (0).2 in 11 and (0).2 in 297
  have eq11442 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq114 eq158 -- superposition 158,114, 114 into 158, unify on (0).2 in 114 and (0).2 in 158
  have eq11543 (X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2)) = (X4 ◇ (X5 ◇ (X4 ◇ X5))) := superpose eq11 eq11442 -- superposition 11442,11, 11 into 11442, unify on (0).2 in 11 and (0).1 in 11442
  have eq11704 (X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) ≠ ((X3 ◇ sK2) ◇ ((X4 ◇ X3) ◇ X3)) := superpose eq11442 eq444 -- superposition 444,11442, 11442 into 444, unify on (0).2 in 11442 and (0).2 in 444
  subsumption eq11704 eq11543


@[equational_result]
theorem Equation4457_implies_Equation4591 (G : Type*) [Magma G] (h : Equation4457 G) : Equation4591 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = ((X3 ◇ X1) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : ((sK0 ◇ sK0) ◇ sK0) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq37 (X0 X1 : G) : (X1 ◇ (sK1 ◇ X1)) ≠ ((X0 ◇ sK0) ◇ sK0) := superpose eq13 eq17 -- superposition 17,13, 13 into 17, unify on (0).2 in 13 and (0).1 in 17
  have eq115 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1.2 in 16
  have eq164 (X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ X5) = ((X1 ◇ X5) ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq11153 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq115 eq164 -- superposition 164,115, 115 into 164, unify on (0).2 in 115 and (0).2 in 164
  have eq11253 (X1 X2 X3 X4 : G) : (X2 ◇ (X1 ◇ X2)) = (X3 ◇ (X4 ◇ (X3 ◇ X4))) := superpose eq9 eq11153 -- superposition 11153,9, 9 into 11153, unify on (0).2 in 9 and (0).1 in 11153
  have eq11410 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) ≠ (X3 ◇ (sK1 ◇ X3)) := superpose eq11153 eq37 -- superposition 37,11153, 11153 into 37, unify on (0).2 in 11153 and (0).2 in 37
  subsumption eq11410 eq11253


@[equational_result]
theorem Equation4457_implies_Equation4383 (G : Type*) [Magma G] (h : Equation4457 G) : Equation4383 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq61 (X0 X1 : G) : (X1 ◇ (sK1 ◇ X1)) ≠ (X0 ◇ (sK0 ◇ X0)) := superpose eq16 eq17 -- superposition 17,16, 16 into 17, unify on (0).2 in 16 and (0).1 in 17
  have eq114 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1.2 in 16
  have eq158 (X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ X5) = ((X1 ◇ X5) ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq197 (X1 X2 : G) : ((X1 ◇ sK1) ◇ sK1) ≠ (X2 ◇ (sK0 ◇ X2)) := superpose eq9 eq61 -- superposition 61,9, 9 into 61, unify on (0).2 in 9 and (0).1 in 61
  have eq297 (X1 X2 : G) : ((X1 ◇ sK0) ◇ sK0) ≠ ((X2 ◇ sK1) ◇ sK1) := superpose eq9 eq197 -- superposition 197,9, 9 into 197, unify on (0).2 in 9 and (0).2 in 197
  have eq444 (X1 X2 X3 : G) : ((X1 ◇ sK1) ◇ ((X2 ◇ X1) ◇ X1)) ≠ ((X3 ◇ sK0) ◇ sK0) := superpose eq11 eq297 -- superposition 297,11, 11 into 297, unify on (0).2 in 11 and (0).2 in 297
  have eq11442 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq114 eq158 -- superposition 158,114, 114 into 158, unify on (0).2 in 114 and (0).2 in 158
  have eq11543 (X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2)) = (X4 ◇ (X5 ◇ (X4 ◇ X5))) := superpose eq11 eq11442 -- superposition 11442,11, 11 into 11442, unify on (0).2 in 11 and (0).1 in 11442
  have eq11704 (X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) ≠ ((X3 ◇ sK1) ◇ ((X4 ◇ X3) ◇ X3)) := superpose eq11442 eq444 -- superposition 444,11442, 11442 into 444, unify on (0).2 in 11442 and (0).2 in 444
  subsumption eq11704 eq11543


@[equational_result]
theorem Equation4457_implies_Equation4452 (G : Type*) [Magma G] (h : Equation4457 G) : Equation4452 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK0 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq61 (X0 X1 : G) : (X1 ◇ (sK0 ◇ X1)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq16 eq17 -- superposition 17,16, 16 into 17, unify on (0).2 in 16 and (0).1 in 17
  have eq66 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).1.2 in 9
  have eq114 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1.2 in 16
  have eq158 (X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ X5) = ((X1 ◇ X5) ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq197 (X1 X2 : G) : ((X1 ◇ sK0) ◇ sK0) ≠ (X2 ◇ (sK1 ◇ X2)) := superpose eq9 eq61 -- superposition 61,9, 9 into 61, unify on (0).2 in 9 and (0).1 in 61
  have eq291 (X0 X1 X2 : G) : ((X0 ◇ sK1) ◇ (X1 ◇ (X0 ◇ X1))) ≠ ((X2 ◇ sK0) ◇ sK0) := superpose eq16 eq197 -- superposition 197,16, 16 into 197, unify on (0).2 in 16 and (0).2.2 in 197
  have eq11452 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq114 eq158 -- superposition 158,114, 114 into 158, unify on (0).2 in 114 and (0).2 in 158
  have eq11557 (X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ (X3 ◇ (X2 ◇ X3))) = (X4 ◇ (X5 ◇ (X4 ◇ X5))) := superpose eq66 eq11452 -- superposition 11452,66, 66 into 11452, unify on (0).2 in 66 and (0).1 in 11452
  have eq11715 (X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) ≠ ((X3 ◇ sK1) ◇ (X4 ◇ (X3 ◇ X4))) := superpose eq11452 eq291 -- superposition 291,11452, 11452 into 291, unify on (0).2 in 11452 and (0).2 in 291
  subsumption eq11715 eq11557


@[equational_result]
theorem Equation4457_implies_Equation4316 (G : Type*) [Magma G] (h : Equation4457 G) : Equation4316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq13 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = ((X3 ◇ X1) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X0) ◇ X3)) = (((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq20 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X1) = ((X2 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq60 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  have eq67 (X0 X1 : G) : (X0 ◇ (sK1 ◇ X0)) ≠ (X1 ◇ (sK2 ◇ X1)) := superpose eq16 eq60 -- superposition 60,16, 16 into 60, unify on (0).2 in 16 and (0).1 in 60
  have eq120 (X1 X2 : G) : (X2 ◇ (sK2 ◇ X2)) ≠ ((X1 ◇ sK1) ◇ sK1) := superpose eq9 eq67 -- superposition 67,9, 9 into 67, unify on (0).2 in 9 and (0).1 in 67
  have eq287 (X1 X2 : G) : ((X1 ◇ sK2) ◇ sK2) ≠ ((X2 ◇ sK1) ◇ sK1) := superpose eq9 eq120 -- superposition 120,9, 9 into 120, unify on (0).2 in 9 and (0).1 in 120
  have eq355 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2 in 14
  have eq492 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X3)) = (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X1)) := superpose eq20 eq16 -- superposition 16,20, 20 into 16, unify on (0).2 in 20 and (0).1.2 in 16
  have eq10007 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X4 ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq355 eq492 -- superposition 492,355, 355 into 492, unify on (0).2 in 355 and (0).2 in 492
  have eq10687 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X3 ◇ X0) ◇ X2)) = ((X4 ◇ X1) ◇ X1) := superpose eq492 eq10007 -- superposition 10007,492, 492 into 10007, unify on (0).2 in 492 and (0).2 in 10007
  have eq10730 (X1 X2 X3 X4 : G) : ((X4 ◇ sK2) ◇ sK2) ≠ (X1 ◇ ((X2 ◇ (X3 ◇ sK1)) ◇ X1)) := superpose eq10007 eq287 -- superposition 287,10007, 10007 into 287, unify on (0).2 in 10007 and (0).2 in 287
  subsumption eq10730 eq10687


@[equational_result]
theorem Equation4457_implies_Equation4656 (G : Type*) [Magma G] (h : Equation4457 G) : Equation4656 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = ((X3 ◇ X1) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq37 (X0 X1 : G) : (X1 ◇ (sK2 ◇ X1)) ≠ ((X0 ◇ sK1) ◇ sK1) := superpose eq13 eq17 -- superposition 17,13, 13 into 17, unify on (0).2 in 13 and (0).1 in 17
  have eq115 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1.2 in 16
  have eq164 (X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ X5) = ((X1 ◇ X5) ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq11153 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq115 eq164 -- superposition 164,115, 115 into 164, unify on (0).2 in 115 and (0).2 in 164
  have eq11253 (X1 X2 X3 X4 : G) : (X2 ◇ (X1 ◇ X2)) = (X3 ◇ (X4 ◇ (X3 ◇ X4))) := superpose eq9 eq11153 -- superposition 11153,9, 9 into 11153, unify on (0).2 in 9 and (0).1 in 11153
  have eq11410 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) ≠ (X3 ◇ (sK2 ◇ X3)) := superpose eq11153 eq37 -- superposition 37,11153, 11153 into 37, unify on (0).2 in 11153 and (0).2 in 37
  subsumption eq11410 eq11253


@[equational_result]
theorem Equation4457_implies_Equation4658 (G : Type*) [Magma G] (h : Equation4457 G) : Equation4658 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ (X0 ◇ (sK0 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq19 (X1 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ ((X1 ◇ sK0) ◇ sK0) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq115 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1.2 in 16
  have eq164 (X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ X5) = ((X1 ◇ X5) ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq11137 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq115 eq164 -- superposition 164,115, 115 into 164, unify on (0).2 in 115 and (0).2 in 164
  have eq11394 (X1 X2 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ (X1 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq11137 eq19 -- superposition 19,11137, 11137 into 19, unify on (0).2 in 11137 and (0).2 in 19
  subsumption eq11394 eq11137


@[equational_result]
theorem Equation4457_implies_Equation4432 (G : Type*) [Magma G] (h : Equation4457 G) : Equation4432 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK0 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq61 (X0 X1 : G) : (X1 ◇ (sK0 ◇ X1)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq16 eq17 -- superposition 17,16, 16 into 17, unify on (0).2 in 16 and (0).1 in 17
  have eq66 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).1.2 in 9
  have eq114 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1.2 in 16
  have eq158 (X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ X5) = ((X1 ◇ X5) ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq197 (X1 X2 : G) : ((X1 ◇ sK0) ◇ sK0) ≠ (X2 ◇ (sK1 ◇ X2)) := superpose eq9 eq61 -- superposition 61,9, 9 into 61, unify on (0).2 in 9 and (0).1 in 61
  have eq291 (X0 X1 X2 : G) : ((X0 ◇ sK1) ◇ (X1 ◇ (X0 ◇ X1))) ≠ ((X2 ◇ sK0) ◇ sK0) := superpose eq16 eq197 -- superposition 197,16, 16 into 197, unify on (0).2 in 16 and (0).2.2 in 197
  have eq11452 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq114 eq158 -- superposition 158,114, 114 into 158, unify on (0).2 in 114 and (0).2 in 158
  have eq11557 (X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ (X3 ◇ (X2 ◇ X3))) = (X4 ◇ (X5 ◇ (X4 ◇ X5))) := superpose eq66 eq11452 -- superposition 11452,66, 66 into 11452, unify on (0).2 in 66 and (0).1 in 11452
  have eq11715 (X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) ≠ ((X3 ◇ sK1) ◇ (X4 ◇ (X3 ◇ X4))) := superpose eq11452 eq291 -- superposition 291,11452, 11452 into 291, unify on (0).2 in 11452 and (0).2 in 291
  subsumption eq11715 eq11557


@[equational_result]
theorem Equation4457_implies_Equation4450 (G : Type*) [Magma G] (h : Equation4457 G) : Equation4450 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq61 (X0 X1 : G) : (X1 ◇ (sK2 ◇ X1)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq16 eq17 -- superposition 17,16, 16 into 17, unify on (0).2 in 16 and (0).1 in 17
  have eq114 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1.2 in 16
  have eq158 (X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ X5) = ((X1 ◇ X5) ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq197 (X1 X2 : G) : ((X1 ◇ sK2) ◇ sK2) ≠ (X2 ◇ (sK1 ◇ X2)) := superpose eq9 eq61 -- superposition 61,9, 9 into 61, unify on (0).2 in 9 and (0).1 in 61
  have eq297 (X1 X2 : G) : ((X1 ◇ sK1) ◇ sK1) ≠ ((X2 ◇ sK2) ◇ sK2) := superpose eq9 eq197 -- superposition 197,9, 9 into 197, unify on (0).2 in 9 and (0).2 in 197
  have eq444 (X1 X2 X3 : G) : ((X1 ◇ sK2) ◇ ((X2 ◇ X1) ◇ X1)) ≠ ((X3 ◇ sK1) ◇ sK1) := superpose eq11 eq297 -- superposition 297,11, 11 into 297, unify on (0).2 in 11 and (0).2 in 297
  have eq11438 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq114 eq158 -- superposition 158,114, 114 into 158, unify on (0).2 in 114 and (0).2 in 158
  have eq11539 (X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2)) = (X4 ◇ (X5 ◇ (X4 ◇ X5))) := superpose eq11 eq11438 -- superposition 11438,11, 11 into 11438, unify on (0).2 in 11 and (0).1 in 11438
  have eq11700 (X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) ≠ ((X3 ◇ sK2) ◇ ((X4 ◇ X3) ◇ X3)) := superpose eq11438 eq444 -- superposition 444,11438, 11438 into 444, unify on (0).2 in 11438 and (0).2 in 444
  subsumption eq11700 eq11539


@[equational_result]
theorem Equation4457_implies_Equation4440 (G : Type*) [Magma G] (h : Equation4457 G) : Equation4440 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq61 (X0 X1 : G) : (X1 ◇ (sK2 ◇ X1)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq16 eq17 -- superposition 17,16, 16 into 17, unify on (0).2 in 16 and (0).1 in 17
  have eq114 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1.2 in 16
  have eq158 (X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ X5) = ((X1 ◇ X5) ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq197 (X1 X2 : G) : ((X1 ◇ sK2) ◇ sK2) ≠ (X2 ◇ (sK1 ◇ X2)) := superpose eq9 eq61 -- superposition 61,9, 9 into 61, unify on (0).2 in 9 and (0).1 in 61
  have eq297 (X1 X2 : G) : ((X1 ◇ sK1) ◇ sK1) ≠ ((X2 ◇ sK2) ◇ sK2) := superpose eq9 eq197 -- superposition 197,9, 9 into 197, unify on (0).2 in 9 and (0).2 in 197
  have eq444 (X1 X2 X3 : G) : ((X1 ◇ sK2) ◇ ((X2 ◇ X1) ◇ X1)) ≠ ((X3 ◇ sK1) ◇ sK1) := superpose eq11 eq297 -- superposition 297,11, 11 into 297, unify on (0).2 in 11 and (0).2 in 297
  have eq11442 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq114 eq158 -- superposition 158,114, 114 into 158, unify on (0).2 in 114 and (0).2 in 158
  have eq11543 (X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2)) = (X4 ◇ (X5 ◇ (X4 ◇ X5))) := superpose eq11 eq11442 -- superposition 11442,11, 11 into 11442, unify on (0).2 in 11 and (0).1 in 11442
  have eq11704 (X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) ≠ ((X3 ◇ sK2) ◇ ((X4 ◇ X3) ◇ X3)) := superpose eq11442 eq444 -- superposition 444,11442, 11442 into 444, unify on (0).2 in 11442 and (0).2 in 444
  subsumption eq11704 eq11543


@[equational_result]
theorem Equation4457_implies_Equation4467 (G : Type*) [Magma G] (h : Equation4457 G) : Equation4467 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK3) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK3 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq61 (X0 X1 : G) : (X1 ◇ (sK3 ◇ X1)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq16 eq17 -- superposition 17,16, 16 into 17, unify on (0).2 in 16 and (0).1 in 17
  have eq114 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1.2 in 16
  have eq158 (X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ X5) = ((X1 ◇ X5) ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq197 (X1 X2 : G) : ((X1 ◇ sK3) ◇ sK3) ≠ (X2 ◇ (sK1 ◇ X2)) := superpose eq9 eq61 -- superposition 61,9, 9 into 61, unify on (0).2 in 9 and (0).1 in 61
  have eq297 (X1 X2 : G) : ((X1 ◇ sK1) ◇ sK1) ≠ ((X2 ◇ sK3) ◇ sK3) := superpose eq9 eq197 -- superposition 197,9, 9 into 197, unify on (0).2 in 9 and (0).2 in 197
  have eq444 (X1 X2 X3 : G) : ((X1 ◇ sK3) ◇ ((X2 ◇ X1) ◇ X1)) ≠ ((X3 ◇ sK1) ◇ sK1) := superpose eq11 eq297 -- superposition 297,11, 11 into 297, unify on (0).2 in 11 and (0).2 in 297
  have eq11442 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq114 eq158 -- superposition 158,114, 114 into 158, unify on (0).2 in 114 and (0).2 in 158
  have eq11543 (X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2)) = (X4 ◇ (X5 ◇ (X4 ◇ X5))) := superpose eq11 eq11442 -- superposition 11442,11, 11 into 11442, unify on (0).2 in 11 and (0).1 in 11442
  have eq11704 (X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) ≠ ((X3 ◇ sK3) ◇ ((X4 ◇ X3) ◇ X3)) := superpose eq11442 eq444 -- superposition 444,11442, 11442 into 444, unify on (0).2 in 11442 and (0).2 in 444
  subsumption eq11704 eq11543


@[equational_result]
theorem Equation723_implies_Equation832 (G : Type*) [Magma G] (h : Equation723 G) : Equation832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = (X2 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq19 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3))) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3))) = X3 := superpose eq15 eq18 -- forward demodulation 18,15
  have eq26 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq42 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ X0)) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq49 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X0))) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.2 in 9
  have eq120 (X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1) = (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq19 eq26 -- superposition 26,19, 19 into 26, unify on (0).2 in 19 and (0).1.2 in 26
  have eq134 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq12 eq120 -- forward demodulation 120,12
  have eq308 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))) = (X0 ◇ X2) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).1.2 in 42
  have eq364 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = (X0 ◇ (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))))) := superpose eq42 eq11 -- superposition 11,42, 42 into 11, unify on (0).2 in 42 and (0).2.2 in 11
  have eq403 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq308 eq134 -- backward demodulation 134,308
  have eq458 (X0 X2 X3 : G) : (X0 ◇ X2) = (X3 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2)))) := superpose eq403 eq308 -- backward demodulation 308,403
  have eq532 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X3 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq403 eq364 -- forward demodulation 364,403
  have eq533 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq458 eq532 -- forward demodulation 532,458
  have eq534 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))) := superpose eq533 eq10 -- backward demodulation 10,533
  have eq535 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq403 eq534 -- forward demodulation 534,403
  subsumption eq535 eq49


@[equational_result]
theorem Equation723_implies_Equation4320 (G : Type*) [Magma G] (h : Equation723 G) : Equation4320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = (X2 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq19 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3))) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3))) = X3 := superpose eq15 eq18 -- forward demodulation 18,15
  have eq26 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq42 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ X0)) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq120 (X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1) = (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq19 eq26 -- superposition 26,19, 19 into 26, unify on (0).2 in 19 and (0).1.2 in 26
  have eq134 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq12 eq120 -- forward demodulation 120,12
  have eq308 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))) = (X0 ◇ X2) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).1.2 in 42
  have eq364 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = (X0 ◇ (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))))) := superpose eq42 eq11 -- superposition 11,42, 42 into 11, unify on (0).2 in 42 and (0).2.2 in 11
  have eq403 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq308 eq134 -- backward demodulation 134,308
  have eq458 (X0 X2 X3 : G) : (X0 ◇ X2) = (X3 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2)))) := superpose eq403 eq308 -- backward demodulation 308,403
  have eq532 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X3 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq403 eq364 -- forward demodulation 364,403
  have eq533 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := superpose eq458 eq532 -- forward demodulation 532,458
  have eq829 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq533 eq10 -- superposition 10,533, 533 into 10, unify on (0).2 in 533 and (0).2 in 10
  subsumption eq829 rfl


@[equational_result]
theorem Equation723_implies_Equation65 (G : Type*) [Magma G] (h : Equation723 G) : Equation65 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = (X2 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq19 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3))) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3))) = X3 := superpose eq15 eq18 -- forward demodulation 18,15
  have eq26 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq42 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ X0)) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq49 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X0))) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.2 in 9
  have eq88 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq49 eq49 -- superposition 49,49, 49 into 49, unify on (0).2 in 49 and (0).1.2 in 49
  have eq120 (X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1) = (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq19 eq26 -- superposition 26,19, 19 into 26, unify on (0).2 in 19 and (0).1.2 in 26
  have eq134 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq12 eq120 -- forward demodulation 120,12
  have eq144 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq88 eq9 -- superposition 9,88, 88 into 9, unify on (0).2 in 88 and (0).1.2.2 in 9
  have eq308 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))) = (X0 ◇ X2) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).1.2 in 42
  have eq364 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = (X0 ◇ (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))))) := superpose eq42 eq11 -- superposition 11,42, 42 into 11, unify on (0).2 in 42 and (0).2.2 in 11
  have eq403 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq308 eq134 -- backward demodulation 134,308
  have eq458 (X0 X2 X3 : G) : (X0 ◇ X2) = (X3 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2)))) := superpose eq403 eq308 -- backward demodulation 308,403
  have eq532 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X3 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq403 eq364 -- forward demodulation 364,403
  have eq533 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := superpose eq458 eq532 -- forward demodulation 532,458
  have eq813 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq533 eq144 -- superposition 144,533, 533 into 144, unify on (0).2 in 533 and (0).1.2 in 144
  have eq1017 : sK0 ≠ sK0 := superpose eq813 eq10 -- superposition 10,813, 813 into 10, unify on (0).2 in 813 and (0).2 in 10
  subsumption eq1017 rfl


@[equational_result]
theorem Equation723_implies_Equation872 (G : Type*) [Magma G] (h : Equation723 G) : Equation872 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = ((X3 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = (X2 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq19 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3))) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3))) = X3 := superpose eq15 eq18 -- forward demodulation 18,15
  have eq26 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq38 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X1)))))) = ((X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X1)))) ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X1)))))) := superpose eq11 eq26 -- superposition 26,11, 11 into 26, unify on (0).2 in 11 and (0).1.2.1 in 26
  have eq40 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1.2.1 in 26
  have eq42 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ X0)) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq49 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X0))) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.2 in 9
  have eq88 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq49 eq49 -- superposition 49,49, 49 into 49, unify on (0).2 in 49 and (0).1.2 in 49
  have eq120 (X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1) = (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq19 eq26 -- superposition 26,19, 19 into 26, unify on (0).2 in 19 and (0).1.2 in 26
  have eq134 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq12 eq120 -- forward demodulation 120,12
  have eq144 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq88 eq9 -- superposition 9,88, 88 into 9, unify on (0).2 in 88 and (0).1.2.2 in 9
  have eq168 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X1)))) ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X1)))))) = ((X4 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X1)))))) ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X1)))))) := superpose eq11 eq15 -- superposition 15,11, 11 into 15, unify on (0).2 in 11 and (0).1.1.2.1 in 15
  have eq234 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq144 eq19 -- superposition 19,144, 144 into 19, unify on (0).2 in 144 and (0).1.1.2.2.1 in 19
  have eq235 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq144 eq26 -- superposition 26,144, 144 into 26, unify on (0).2 in 144 and (0).1.2.1 in 26
  have eq237 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq144 eq49 -- superposition 49,144, 144 into 49, unify on (0).2 in 144 and (0).1.2.2 in 49
  have eq308 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))) = (X0 ◇ X2) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).1.2 in 42
  have eq309 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X1)))))) = (X0 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X1))) := superpose eq11 eq42 -- superposition 42,11, 11 into 42, unify on (0).2 in 11 and (0).1.2 in 42
  have eq311 (X0 X1 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq49 eq42 -- superposition 42,49, 49 into 42, unify on (0).2 in 49 and (0).1.2 in 42
  have eq363 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = ((X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) := superpose eq42 eq13 -- superposition 13,42, 42 into 13, unify on (0).2 in 42 and (0).2.1 in 13
  have eq364 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = (X0 ◇ (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))))) := superpose eq42 eq11 -- superposition 11,42, 42 into 11, unify on (0).2 in 42 and (0).2.2 in 11
  have eq403 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq308 eq134 -- backward demodulation 134,308
  have eq419 (X0 X1 X2 X4 : G) : (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))))) := superpose eq403 eq38 -- backward demodulation 38,403
  have eq420 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq403 eq40 -- backward demodulation 40,403
  have eq447 (X0 X1 X2 X4 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))))) = ((X4 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))))) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))))) := superpose eq403 eq168 -- backward demodulation 168,403
  have eq458 (X0 X2 X3 : G) : (X0 ◇ X2) = (X3 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2)))) := superpose eq403 eq308 -- backward demodulation 308,403
  have eq471 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq458 eq235 -- backward demodulation 235,458
  have eq473 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq471 eq234 -- backward demodulation 234,471
  have eq475 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))))) = ((X2 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))))) := superpose eq473 eq447 -- backward demodulation 447,473
  have eq480 (X0 X1 X2 X4 : G) : (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))))) = (X0 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq403 eq309 -- forward demodulation 309,403
  have eq481 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))))) = (X0 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq480 eq419 -- backward demodulation 419,480
  have eq482 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ X1))) = ((X2 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))))) := superpose eq481 eq475 -- backward demodulation 475,481
  have eq530 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X3 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq403 eq363 -- forward demodulation 363,403
  have eq531 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq458 eq530 -- forward demodulation 530,458
  have eq532 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X3 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq403 eq364 -- forward demodulation 364,403
  have eq533 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq458 eq532 -- forward demodulation 532,458
  have eq634 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq144 eq403 -- superposition 403,144, 144 into 403, unify on (0).2 in 144 and (0).1.1 in 403
  have eq637 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq42 eq403 -- superposition 403,42, 42 into 403, unify on (0).2 in 42 and (0).1.1 in 403
  have eq827 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq533 eq403 -- superposition 403,533, 533 into 403, unify on (0).2 in 533 and (0).1.1 in 403
  have eq866 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq237 eq827 -- forward demodulation 827,237
  have eq868 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ X1))) = ((X2 ◇ (X1 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))))) := superpose eq866 eq482 -- backward demodulation 482,866
  have eq877 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq866 eq637 -- backward demodulation 637,866
  have eq879 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ X1))) = ((X2 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1)))))) := superpose eq866 eq868 -- forward demodulation 868,866
  have eq880 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ X1))) = ((X2 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))))) := superpose eq634 eq879 -- forward demodulation 879,634
  have eq881 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ X1))) = ((X2 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq458 eq880 -- forward demodulation 880,458
  have eq923 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq877 eq420 -- backward demodulation 420,877
  have eq2450 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X2)))))) := superpose eq923 eq311 -- superposition 311,923, 923 into 311, unify on (0).2 in 923 and (0).2.2.2.2 in 311
  have eq2713 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X2)))))) := superpose eq531 eq2450 -- forward demodulation 2450,531
  have eq2714 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq480 eq2713 -- forward demodulation 2713,480
  have eq3118 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq311 eq881 -- superposition 881,311, 311 into 881, unify on (0).2 in 311 and (0).1.2 in 881
  have eq3291 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq2714 eq3118 -- forward demodulation 3118,2714
  have eq3292 (X1 X2 : G) : (X2 ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq144 eq3291 -- forward demodulation 3291,144
  have eq3293 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq3292 eq10 -- backward demodulation 10,3292
  subsumption eq3293 eq144


@[equational_result]
theorem Equation723_implies_Equation1506 (G : Type*) [Magma G] (h : Equation723 G) : Equation1506 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq46 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ X0)) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).2 in 26
  have eq57 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X0))) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.2 in 9
  have eq94 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq57 eq12 -- superposition 12,57, 57 into 12, unify on (0).2 in 57 and (0).1.1 in 12
  have eq102 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq57 eq94 -- forward demodulation 94,57
  have eq367 (X0 : G) : sK0 ≠ ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ sK0))) := superpose eq46 eq10 -- superposition 10,46, 46 into 10, unify on (0).2 in 46 and (0).2.2 in 10
  subsumption eq367 eq102


@[equational_result]
theorem Equation723_implies_Equation1478 (G : Type*) [Magma G] (h : Equation723 G) : Equation1478 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq42 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ X0)) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq49 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X0))) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.2 in 9
  have eq94 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq49 eq12 -- superposition 12,49, 49 into 12, unify on (0).2 in 49 and (0).1.1 in 12
  have eq102 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq49 eq94 -- forward demodulation 94,49
  have eq367 (X0 : G) : sK0 ≠ ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ sK0))) := superpose eq42 eq10 -- superposition 10,42, 42 into 10, unify on (0).2 in 42 and (0).2.2 in 10
  subsumption eq367 eq102


@[equational_result]
theorem Equation723_implies_Equation909 (G : Type*) [Magma G] (h : Equation723 G) : Equation909 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = (X2 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq19 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3))) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3))) = X3 := superpose eq15 eq18 -- forward demodulation 18,15
  have eq26 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq42 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ X0)) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq49 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X0))) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.2 in 9
  have eq88 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq49 eq49 -- superposition 49,49, 49 into 49, unify on (0).2 in 49 and (0).1.2 in 49
  have eq120 (X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1) = (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq19 eq26 -- superposition 26,19, 19 into 26, unify on (0).2 in 19 and (0).1.2 in 26
  have eq134 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq12 eq120 -- forward demodulation 120,12
  have eq144 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq88 eq9 -- superposition 9,88, 88 into 9, unify on (0).2 in 88 and (0).1.2.2 in 9
  have eq237 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq144 eq49 -- superposition 49,144, 144 into 49, unify on (0).2 in 144 and (0).1.2.2 in 49
  have eq308 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))) = (X0 ◇ X2) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).1.2 in 42
  have eq364 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = (X0 ◇ (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))))) := superpose eq42 eq11 -- superposition 11,42, 42 into 11, unify on (0).2 in 42 and (0).2.2 in 11
  have eq403 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq308 eq134 -- backward demodulation 134,308
  have eq458 (X0 X2 X3 : G) : (X0 ◇ X2) = (X3 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2)))) := superpose eq403 eq308 -- backward demodulation 308,403
  have eq532 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X3 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq403 eq364 -- forward demodulation 364,403
  have eq533 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq458 eq532 -- forward demodulation 532,458
  have eq827 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq533 eq403 -- superposition 403,533, 533 into 403, unify on (0).2 in 533 and (0).1.1 in 403
  have eq866 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := superpose eq237 eq827 -- forward demodulation 827,237
  have eq878 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq866 eq10 -- backward demodulation 10,866
  subsumption eq878 eq144


@[equational_result]
theorem Equation723_implies_Equation3877 (G : Type*) [Magma G] (h : Equation723 G) : Equation3877 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = (X2 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq19 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3))) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3))) = X3 := superpose eq15 eq18 -- forward demodulation 18,15
  have eq26 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq42 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ X0)) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq49 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X0))) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.2 in 9
  have eq88 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq49 eq49 -- superposition 49,49, 49 into 49, unify on (0).2 in 49 and (0).1.2 in 49
  have eq94 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq49 eq12 -- superposition 12,49, 49 into 12, unify on (0).2 in 49 and (0).1.1 in 12
  have eq102 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq49 eq94 -- forward demodulation 94,49
  have eq120 (X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1) = (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq19 eq26 -- superposition 26,19, 19 into 26, unify on (0).2 in 19 and (0).1.2 in 26
  have eq134 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq12 eq120 -- forward demodulation 120,12
  have eq144 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq88 eq9 -- superposition 9,88, 88 into 9, unify on (0).2 in 88 and (0).1.2.2 in 9
  have eq308 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))) = (X0 ◇ X2) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).1.2 in 42
  have eq364 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = (X0 ◇ (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))))) := superpose eq42 eq11 -- superposition 11,42, 42 into 11, unify on (0).2 in 42 and (0).2.2 in 11
  have eq403 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq308 eq134 -- backward demodulation 134,308
  have eq458 (X0 X2 X3 : G) : (X0 ◇ X2) = (X3 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2)))) := superpose eq403 eq308 -- backward demodulation 308,403
  have eq532 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X3 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq403 eq364 -- forward demodulation 364,403
  have eq533 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq458 eq532 -- forward demodulation 532,458
  have eq534 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq533 eq10 -- backward demodulation 10,533
  have eq849 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X2 ◇ (X1 ◇ X1)))) := superpose eq533 eq102 -- superposition 102,533, 533 into 102, unify on (0).2 in 533 and (0).1.1 in 102
  have eq897 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq144 eq849 -- forward demodulation 849,144
  have eq1436 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq897 eq534 -- superposition 534,897, 897 into 534, unify on (0).2 in 897 and (0).2 in 534
  subsumption eq1436 rfl


@[equational_result]
theorem Equation723_implies_Equation1426 (G : Type*) [Magma G] (h : Equation723 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.1 in 8
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq25 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2.2 in 10
  have eq41 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ X0)) := superpose eq25 eq25 -- superposition 25,25, 25 into 25, unify on (0).2 in 25 and (0).1 in 25
  have eq48 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X0))) = X0 := superpose eq25 eq8 -- superposition 8,25, 25 into 8, unify on (0).2 in 25 and (0).1.2 in 8
  have eq93 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq48 eq11 -- superposition 11,48, 48 into 11, unify on (0).2 in 48 and (0).1.1 in 11
  have eq101 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq48 eq93 -- forward demodulation 93,48
  have eq349 (X0 : G) : sK0 ≠ ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ sK0))) := superpose eq41 eq9 -- superposition 9,41, 41 into 9, unify on (0).2 in 41 and (0).2.2 in 9
  subsumption eq349 eq101


@[equational_result]
theorem Equation723_implies_Equation4080 (G : Type*) [Magma G] (h : Equation723 G) : Equation4080 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = (X2 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq19 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3))) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3))) = X3 := superpose eq15 eq18 -- forward demodulation 18,15
  have eq26 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq42 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ X0)) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq49 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X0))) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.2 in 9
  have eq88 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq49 eq49 -- superposition 49,49, 49 into 49, unify on (0).2 in 49 and (0).1.2 in 49
  have eq120 (X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1) = (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq19 eq26 -- superposition 26,19, 19 into 26, unify on (0).2 in 19 and (0).1.2 in 26
  have eq134 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq12 eq120 -- forward demodulation 120,12
  have eq308 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))) = (X0 ◇ X2) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).1.2 in 42
  have eq403 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq308 eq134 -- backward demodulation 134,308
  have eq464 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq403 eq10 -- backward demodulation 10,403
  subsumption eq464 eq88


@[equational_result]
theorem Equation723_implies_Equation4666 (G : Type*) [Magma G] (h : Equation723 G) : Equation4666 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = (X2 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq19 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3))) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3))) = X3 := superpose eq15 eq18 -- forward demodulation 18,15
  have eq26 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq42 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ X0)) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq120 (X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1) = (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq19 eq26 -- superposition 26,19, 19 into 26, unify on (0).2 in 19 and (0).1.2 in 26
  have eq134 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq12 eq120 -- forward demodulation 120,12
  have eq308 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))) = (X0 ◇ X2) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).1.2 in 42
  have eq403 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq308 eq134 -- backward demodulation 134,308
  have eq464 : ((sK0 ◇ sK1) ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq403 eq10 -- backward demodulation 10,403
  subsumption eq464 eq403


@[equational_result]
theorem Equation723_implies_Equation4100 (G : Type*) [Magma G] (h : Equation723 G) : Equation4100 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = (X2 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq19 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3))) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3))) = X3 := superpose eq15 eq18 -- forward demodulation 18,15
  have eq26 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq42 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ X0)) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq120 (X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1) = (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq19 eq26 -- superposition 26,19, 19 into 26, unify on (0).2 in 19 and (0).1.2 in 26
  have eq134 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq12 eq120 -- forward demodulation 120,12
  have eq308 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))) = (X0 ◇ X2) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).1.2 in 42
  have eq403 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq308 eq134 -- backward demodulation 134,308
  have eq641 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq403 eq10 -- superposition 10,403, 403 into 10, unify on (0).2 in 403 and (0).2 in 10
  subsumption eq641 rfl


@[equational_result]
theorem Equation723_implies_Equation364 (G : Type*) [Magma G] (h : Equation723 G) : Equation364 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = (X2 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq19 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3))) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3))) = X3 := superpose eq15 eq18 -- forward demodulation 18,15
  have eq26 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq42 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ X0)) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq120 (X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1) = (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq19 eq26 -- superposition 26,19, 19 into 26, unify on (0).2 in 19 and (0).1.2 in 26
  have eq134 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq12 eq120 -- forward demodulation 120,12
  have eq308 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))) = (X0 ◇ X2) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).1.2 in 42
  have eq403 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq308 eq134 -- backward demodulation 134,308
  have eq649 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq403 eq10 -- superposition 10,403, 403 into 10, unify on (0).2 in 403 and (0).2 in 10
  subsumption eq649 rfl


@[equational_result]
theorem Equation3882_implies_Equation3868 (G : Type*) [Magma G] (h : Equation3882 G) : Equation3868 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq54 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq17 -- superposition 17,27, 27 into 17, unify on (0).2 in 27 and (0).2 in 17
  subsumption eq54 eq27


@[equational_result]
theorem Equation3882_implies_Equation3870 (G : Type*) [Magma G] (h : Equation3882 G) : Equation3870 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = ((X2 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq26 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq48 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq48 eq26


@[equational_result]
theorem Equation3882_implies_Equation3677 (G : Type*) [Magma G] (h : Equation3882 G) : Equation3677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq29 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ X1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq29 eq15


@[equational_result]
theorem Equation3882_implies_Equation3906 (G : Type*) [Magma G] (h : Equation3882 G) : Equation3906 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = ((X2 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq26 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq48 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq48 eq26


@[equational_result]
theorem Equation3882_implies_Equation3907 (G : Type*) [Magma G] (h : Equation3882 G) : Equation3907 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = ((X2 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq26 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq48 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq48 eq26


@[equational_result]
theorem Equation3882_implies_Equation4341 (G : Type*) [Magma G] (h : Equation3882 G) : Equation4341 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq26 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq80 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2.2 in 10
  subsumption eq80 rfl


@[equational_result]
theorem Equation3882_implies_Equation3904 (G : Type*) [Magma G] (h : Equation3882 G) : Equation3904 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK3) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq54 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq17 -- superposition 17,27, 27 into 17, unify on (0).2 in 27 and (0).2 in 17
  subsumption eq54 eq27


@[equational_result]
theorem Equation4465_implies_Equation4450 (G : Type*) [Magma G] (h : Equation4465 G) : Equation4450 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X2 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq201 (X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X5 ◇ (X4 ◇ X5))) := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1 in 12
  have eq233 (X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X2 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).2 in 19
  subsumption eq233 eq201


@[equational_result]
theorem Equation4465_implies_Equation4468 (G : Type*) [Magma G] (h : Equation4465 G) : Equation4468 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK3) ◇ sK4) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X2 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK4 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq201 (X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X5 ◇ (X4 ◇ X5))) := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1 in 12
  have eq238 (X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X2 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).2 in 19
  subsumption eq238 eq201


@[equational_result]
theorem Equation4465_implies_Equation4448 (G : Type*) [Magma G] (h : Equation4465 G) : Equation4448 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X2 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK0 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq201 (X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X5 ◇ (X4 ◇ X5))) := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1 in 12
  have eq238 (X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X2 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).2 in 19
  subsumption eq238 eq201


@[equational_result]
theorem Equation4465_implies_Equation4441 (G : Type*) [Magma G] (h : Equation4465 G) : Equation4441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK2) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X2 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK3 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq201 (X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X5 ◇ (X4 ◇ X5))) := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1 in 12
  have eq238 (X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X2 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).2 in 19
  subsumption eq238 eq201


@[equational_result]
theorem Equation4465_implies_Equation4458 (G : Type*) [Magma G] (h : Equation4465 G) : Equation4458 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X2 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq201 (X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X5 ◇ (X4 ◇ X5))) := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1 in 12
  have eq238 (X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X2 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).2 in 19
  subsumption eq238 eq201


@[equational_result]
theorem Equation4465_implies_Equation4384 (G : Type*) [Magma G] (h : Equation4465 G) : Equation4384 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X2 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq201 (X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X5 ◇ (X4 ◇ X5))) := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1 in 12
  have eq238 (X2 X3 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X2 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).2 in 19
  subsumption eq238 eq201


@[equational_result]
theorem Equation4465_implies_Equation4437 (G : Type*) [Magma G] (h : Equation4465 G) : Equation4437 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X2 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq201 (X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X5 ◇ (X4 ◇ X5))) := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1 in 12
  have eq238 (X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X2 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).2 in 19
  subsumption eq238 eq201


