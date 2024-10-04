import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation3898_implies_Equation3687 (G : Type*) [Magma G] (h : Equation3898 G) : Equation3687 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = ((X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X2)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq16 eq14 -- forward demodulation 14,16
  have eq26 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq71 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (sK1 ◇ sK0)) := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2.1 in 10
  subsumption eq71 eq17


@[equational_result]
theorem Equation3898_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3898 G) : Equation3659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = ((X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X3) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1.2 in 8
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X2)) ◇ X3) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1.2 in 8
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1 in 8
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = (X1 ◇ X1) := superpose eq8 eq11 -- forward demodulation 11,8
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq15 eq13 -- forward demodulation 13,15
  have eq25 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2 in 12
  have eq70 (X0 : G) : (X0 ◇ X0) ≠ ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq25 eq9 -- superposition 9,25, 25 into 9, unify on (0).2 in 25 and (0).1 in 9
  subsumption eq70 eq16


@[equational_result]
theorem Equation3898_implies_Equation3665 (G : Type*) [Magma G] (h : Equation3898 G) : Equation3665 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X2)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq26 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq71 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq71 eq26


@[equational_result]
theorem Equation3898_implies_Equation40 (G : Type*) [Magma G] (h : Equation3898 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X2)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq26 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq71 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq71 eq26


@[equational_result]
theorem Equation3898_implies_Equation3906 (G : Type*) [Magma G] (h : Equation3898 G) : Equation3906 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X2)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq27 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq32 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq32 eq27


@[equational_result]
theorem Equation3898_implies_Equation3894 (G : Type*) [Magma G] (h : Equation3898 G) : Equation3894 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X2)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq55 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq16 -- superposition 16,27, 27 into 16, unify on (0).2 in 27 and (0).2 in 16
  subsumption eq55 eq27


@[equational_result]
theorem Equation3898_implies_Equation3684 (G : Type*) [Magma G] (h : Equation3898 G) : Equation3684 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = ((X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X2)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq16 eq14 -- forward demodulation 14,16
  have eq26 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq79 (X0 : G) : (X0 ◇ X0) ≠ ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).1 in 10
  subsumption eq79 eq17


@[equational_result]
theorem Equation3898_implies_Equation3660 (G : Type*) [Magma G] (h : Equation3898 G) : Equation3660 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = ((X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X2)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq26 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq45 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ X3)) ◇ X2) = (((X2 ◇ (X3 ◇ X3)) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq13 eq16 -- superposition 16,13, 13 into 16, unify on (0).2 in 13 and (0).1.1 in 16
  have eq57 (X0 X1 X3 : G) : (X3 ◇ X3) = ((X3 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq9 eq45 -- forward demodulation 45,9
  have eq71 (X0 : G) : (X0 ◇ X0) ≠ ((X0 ◇ X0) ◇ (sK0 ◇ sK1)) := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).1 in 10
  subsumption eq71 eq57


@[equational_result]
theorem Equation3898_implies_Equation3690 (G : Type*) [Magma G] (h : Equation3898 G) : Equation3690 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = ((X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X2)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq16 eq14 -- forward demodulation 14,16
  have eq26 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq79 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (sK2 ◇ sK0)) := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2.1 in 10
  subsumption eq79 eq17


@[equational_result]
theorem Equation3898_implies_Equation3881 (G : Type*) [Magma G] (h : Equation3898 G) : Equation3881 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X2)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq55 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq16 -- superposition 16,27, 27 into 16, unify on (0).2 in 27 and (0).2 in 16
  subsumption eq55 eq27


@[equational_result]
theorem Equation3898_implies_Equation3663 (G : Type*) [Magma G] (h : Equation3898 G) : Equation3663 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = ((X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X2)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq26 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq45 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ X3)) ◇ X2) = (((X2 ◇ (X3 ◇ X3)) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq13 eq16 -- superposition 16,13, 13 into 16, unify on (0).2 in 13 and (0).1.1 in 16
  have eq57 (X0 X1 X3 : G) : (X3 ◇ X3) = ((X3 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq9 eq45 -- forward demodulation 45,9
  have eq79 (X0 : G) : (X0 ◇ X0) ≠ ((X0 ◇ X0) ◇ (sK1 ◇ sK2)) := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).1 in 10
  subsumption eq79 eq57


@[equational_result]
theorem Equation3898_implies_Equation3873 (G : Type*) [Magma G] (h : Equation3898 G) : Equation3873 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X2)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq55 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq16 -- superposition 16,27, 27 into 16, unify on (0).2 in 27 and (0).2 in 16
  subsumption eq55 eq27


@[equational_result]
theorem Equation3898_implies_Equation3902 (G : Type*) [Magma G] (h : Equation3898 G) : Equation3902 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X2)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq55 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq16 -- superposition 16,27, 27 into 16, unify on (0).2 in 27 and (0).2 in 16
  subsumption eq55 eq27


@[equational_result]
theorem Equation3898_implies_Equation3910 (G : Type*) [Magma G] (h : Equation3898 G) : Equation3910 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X2)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq55 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq16 -- superposition 16,27, 27 into 16, unify on (0).2 in 27 and (0).2 in 16
  subsumption eq55 eq27


@[equational_result]
theorem Equation454_implies_Equation446 (G : Type*) [Magma G] (h : Equation454 G) : Equation446 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2.2 in 9
  have eq27 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq35 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq27 eq27 -- superposition 27,27, 27 into 27, unify on (0).2 in 27 and (0).1.2.2 in 27
  have eq149 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X3 := superpose eq35 eq16 -- superposition 16,35, 35 into 16, unify on (0).2 in 35 and (0).1.2 in 16
  have eq263 : sK0 ≠ sK0 := superpose eq149 eq10 -- superposition 10,149, 149 into 10, unify on (0).2 in 149 and (0).2 in 10
  subsumption eq263 rfl


@[equational_result]
theorem Equation454_implies_Equation413 (G : Type*) [Magma G] (h : Equation454 G) : Equation413 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq27 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq48 : sK0 ≠ sK0 := superpose eq27 eq10 -- superposition 10,27, 27 into 10, unify on (0).2 in 27 and (0).2 in 10
  subsumption eq48 rfl


@[equational_result]
theorem Equation454_implies_Equation429 (G : Type*) [Magma G] (h : Equation454 G) : Equation429 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq27 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq41 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq27 eq12 -- superposition 12,27, 27 into 12, unify on (0).2 in 27 and (0).1 in 12
  have eq102 : sK0 ≠ sK0 := superpose eq41 eq10 -- superposition 10,41, 41 into 10, unify on (0).2 in 41 and (0).2 in 10
  subsumption eq102 rfl


@[equational_result]
theorem Equation2707_implies_Equation4332 (G : Type*) [Magma G] (h : Equation2707 G) : Equation4332 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq21 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq30 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).1.1 in 21
  have eq49 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2)) := superpose eq12 eq30 -- superposition 30,12, 12 into 30, unify on (0).2 in 12 and (0).1.2.1 in 30
  have eq73 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := superpose eq11 eq49 -- superposition 49,11, 11 into 49, unify on (0).2 in 11 and (0).2.2.1 in 49
  have eq172 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq73 eq10 -- superposition 10,73, 73 into 10, unify on (0).2 in 73 and (0).2 in 10
  subsumption eq172 eq73


@[equational_result]
theorem Equation1358_implies_Equation1977 (G : Type*) [Magma G] (h : Equation1358 G) : Equation1977 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = (X3 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X3) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 (X0 X1 X2 X3 X4 : G) : (((X4 ◇ (X0 ◇ X1)) ◇ X4) ◇ X0) = (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq26 (X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ X2)) ◇ X3) ◇ X1) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq36 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X3))) = X1 := superpose eq26 eq23 -- backward demodulation 23,26
  have eq46 (X0 X1 X2 X3 X4 : G) : ((((X3 ◇ X4) ◇ X3) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))) ◇ X4) = X0 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.2 in 12
  have eq61 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := superpose eq9 eq26 -- superposition 26,9, 9 into 26, unify on (0).2 in 9 and (0).1.1.1 in 26
  have eq121 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) = X2 := superpose eq61 eq26 -- superposition 26,61, 61 into 26, unify on (0).2 in 61 and (0).1.1.1 in 26
  have eq128 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X0) ◇ X2) ◇ (X3 ◇ (X1 ◇ X3))) := superpose eq61 eq36 -- superposition 36,61, 61 into 36, unify on (0).2 in 61 and (0).1.2.2.1 in 36
  have eq129 (X0 X1 X4 : G) : ((X4 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X4) = X0 := superpose eq128 eq46 -- backward demodulation 46,128
  have eq155 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = (X3 ◇ (X2 ◇ X3)) := superpose eq129 eq9 -- superposition 9,129, 129 into 9, unify on (0).2 in 129 and (0).1.2.1 in 9
  have eq237 (X0 : G) : sK0 ≠ ((X0 ◇ (sK2 ◇ X0)) ◇ (sK0 ◇ sK2)) := superpose eq155 eq10 -- superposition 10,155, 155 into 10, unify on (0).2 in 155 and (0).2.1 in 10
  subsumption eq237 eq121


@[equational_result]
theorem Equation1171_implies_Equation4073 (G : Type*) [Magma G] (h : Equation1171 G) : Equation4073 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq32 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) ◇ X3)) ◇ X4) = (X1 ◇ X4) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq33 (X0 X1 X2 X3 X4 X5 : G) : ((((X3 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) ◇ X3)) ◇ X4) ◇ X4) ◇ X5) = (X1 ◇ X5) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq42 (X1 X4 X5 : G) : (X1 ◇ X5) = (((X1 ◇ X4) ◇ X4) ◇ X5) := superpose eq32 eq33 -- forward demodulation 33,32
  have eq70 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq42 eq10 -- superposition 10,42, 42 into 10, unify on (0).2 in 42 and (0).2 in 10
  subsumption eq70 rfl


@[equational_result]
theorem Equation1171_implies_Equation4146 (G : Type*) [Magma G] (h : Equation1171 G) : Equation4146 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq32 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) ◇ X3)) ◇ X4) = (X1 ◇ X4) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq33 (X0 X1 X2 X3 X4 X5 : G) : ((((X3 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) ◇ X3)) ◇ X4) ◇ X4) ◇ X5) = (X1 ◇ X5) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq42 (X1 X4 X5 : G) : (X1 ◇ X5) = (((X1 ◇ X4) ◇ X4) ◇ X5) := superpose eq32 eq33 -- forward demodulation 33,32
  have eq70 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq42 eq10 -- superposition 10,42, 42 into 10, unify on (0).2 in 42 and (0).2 in 10
  subsumption eq70 rfl


@[equational_result]
theorem Equation3176_implies_Equation1238 (G : Type*) [Magma G] (h : Equation3176 G) : Equation1238 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq13 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation3176_implies_Equation2087 (G : Type*) [Magma G] (h : Equation3176 G) : Equation2087 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq13 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq11


@[equational_result]
theorem Equation3176_implies_Equation270 (G : Type*) [Magma G] (h : Equation3176 G) : Equation270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation1244_implies_Equation1258 (G : Type*) [Magma G] (h : Equation1244 G) : Equation1258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation1244_implies_Equation1248 (G : Type*) [Magma G] (h : Equation1244 G) : Equation1248 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation4072_implies_Equation4068 (G : Type*) [Magma G] (h : Equation4072 G) : Equation4068 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) = (((X0 ◇ X0) ◇ X2) ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq18 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X0) ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq22 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X3) = (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq32 (X0 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq17 eq22 -- forward demodulation 22,17
  have eq33 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X2) ◇ X3) := superpose eq32 eq15 -- backward demodulation 15,32
  have eq78 (X0 : G) : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ X0) ◇ sK1) := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2.1 in 10
  subsumption eq78 eq33


@[equational_result]
theorem Equation4072_implies_Equation4069 (G : Type*) [Magma G] (h : Equation4072 G) : Equation4069 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) = (((X0 ◇ X0) ◇ X2) ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq18 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X0) ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq22 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X3) = (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq32 (X0 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq17 eq22 -- forward demodulation 22,17
  have eq33 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X2) ◇ X3) := superpose eq32 eq15 -- backward demodulation 15,32
  have eq78 (X0 : G) : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ X0) ◇ sK2) := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2.1 in 10
  subsumption eq78 eq33


@[equational_result]
theorem Equation3679_implies_Equation3709 (G : Type*) [Magma G] (h : Equation3679 G) : Equation3709 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X0 ◇ X3) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X0 X1 X3 : G) : (X3 ◇ X3) = (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq20 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X1) = ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X2 ◇ X4)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq70 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) = ((X3 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X4)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2.1.2 in 12
  have eq71 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq83 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) := superpose eq20 eq70 -- forward demodulation 70,20
  have eq87 (X0 X2 X3 : G) : (X3 ◇ X3) = ((X0 ◇ X3) ◇ (X2 ◇ X2)) := superpose eq83 eq71 -- forward demodulation 71,83
  have eq130 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq87 eq10 -- superposition 10,87, 87 into 10, unify on (0).2 in 87 and (0).2 in 10
  have eq503 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X1 ◇ X3) ◇ (X1 ◇ X3)) := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  have eq631 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq503 -- superposition 503,9, 9 into 503, unify on (0).2 in 9 and (0).2 in 503
  have eq930 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq631 eq130 -- superposition 130,631, 631 into 130, unify on (0).2 in 631 and (0).2 in 130
  subsumption eq930 eq631


@[equational_result]
theorem Equation3679_implies_Equation3663 (G : Type*) [Magma G] (h : Equation3679 G) : Equation3663 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X3 : G) : (X3 ◇ X3) = (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq20 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X1) = ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X2 ◇ X4)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq70 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) = ((X3 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X4)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2.1.2 in 12
  have eq72 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) = ((((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.1 in 9
  have eq83 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) := superpose eq20 eq70 -- forward demodulation 70,20
  have eq88 (X0 X2 X3 : G) : (X2 ◇ X2) = ((X2 ◇ X2) ◇ (X0 ◇ X3)) := superpose eq83 eq72 -- forward demodulation 72,83
  have eq282 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq88 eq10 -- superposition 10,88, 88 into 10, unify on (0).2 in 88 and (0).2 in 10
  subsumption eq282 rfl


@[equational_result]
theorem Equation3679_implies_Equation3694 (G : Type*) [Magma G] (h : Equation3679 G) : Equation3694 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X0 ◇ X3) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X0 X1 X3 : G) : (X3 ◇ X3) = (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq20 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X1) = ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X2 ◇ X4)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq69 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X3) = ((X0 ◇ (X4 ◇ X3)) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2.2 in 12
  have eq70 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) = ((X3 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X4)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2.1.2 in 12
  have eq71 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq83 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) := superpose eq20 eq70 -- forward demodulation 70,20
  have eq86 (X0 X2 X3 X4 : G) : (X3 ◇ X3) = ((X0 ◇ (X4 ◇ X3)) ◇ (X2 ◇ X2)) := superpose eq83 eq69 -- backward demodulation 69,83
  have eq87 (X0 X2 X3 : G) : (X3 ◇ X3) = ((X0 ◇ X3) ◇ (X2 ◇ X2)) := superpose eq83 eq71 -- forward demodulation 71,83
  have eq97 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X2)) = (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) := superpose eq87 eq87 -- superposition 87,87, 87 into 87, unify on (0).2 in 87 and (0).2.1 in 87
  have eq143 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X0) ◇ (X2 ◇ X2)) := superpose eq86 eq97 -- forward demodulation 97,86
  have eq503 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X1 ◇ X3) ◇ (X1 ◇ X3)) := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  have eq631 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq503 -- superposition 503,9, 9 into 503, unify on (0).2 in 9 and (0).2 in 503
  have eq930 (X0 : G) : (X0 ◇ X0) ≠ ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := superpose eq631 eq10 -- superposition 10,631, 631 into 10, unify on (0).2 in 631 and (0).1 in 10
  subsumption eq930 eq143


@[equational_result]
theorem Equation3679_implies_Equation3666 (G : Type*) [Magma G] (h : Equation3679 G) : Equation3666 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = ((X3 ◇ X0) ◇ (X3 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq29 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) = (X2 ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq137 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ sK1) ◇ (X0 ◇ X1)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq464 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq14 eq137 -- superposition 137,14, 14 into 137, unify on (0).2 in 14 and (0).2 in 137
  subsumption eq464 eq29


@[equational_result]
theorem Equation3679_implies_Equation3672 (G : Type*) [Magma G] (h : Equation3679 G) : Equation3672 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X0 ◇ X3) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X0 X1 X3 : G) : (X3 ◇ X3) = (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq20 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X1) = ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X2 ◇ X4)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq70 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) = ((X3 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X4)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2.1.2 in 12
  have eq71 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq83 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) := superpose eq20 eq70 -- forward demodulation 70,20
  have eq87 (X0 X2 X3 : G) : (X3 ◇ X3) = ((X0 ◇ X3) ◇ (X2 ◇ X2)) := superpose eq83 eq71 -- forward demodulation 71,83
  have eq130 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq87 eq10 -- superposition 10,87, 87 into 10, unify on (0).2 in 87 and (0).2 in 10
  have eq503 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X1 ◇ X3) ◇ (X1 ◇ X3)) := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  have eq631 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq503 -- superposition 503,9, 9 into 503, unify on (0).2 in 9 and (0).2 in 503
  have eq930 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq631 eq130 -- superposition 130,631, 631 into 130, unify on (0).2 in 631 and (0).2 in 130
  subsumption eq930 eq631


@[equational_result]
theorem Equation3679_implies_Equation4341 (G : Type*) [Magma G] (h : Equation3679 G) : Equation4341 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X3 : G) : (X3 ◇ X3) = (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq20 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X1) = ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X2 ◇ X4)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq69 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X3) = ((X0 ◇ (X4 ◇ X3)) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2.2 in 12
  have eq70 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) = ((X3 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X4)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2.1.2 in 12
  have eq71 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq83 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) := superpose eq20 eq70 -- forward demodulation 70,20
  have eq86 (X0 X2 X3 X4 : G) : (X3 ◇ X3) = ((X0 ◇ (X4 ◇ X3)) ◇ (X2 ◇ X2)) := superpose eq83 eq69 -- backward demodulation 69,83
  have eq87 (X0 X2 X3 : G) : (X3 ◇ X3) = ((X0 ◇ X3) ◇ (X2 ◇ X2)) := superpose eq83 eq71 -- forward demodulation 71,83
  have eq97 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X2)) = (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) := superpose eq87 eq87 -- superposition 87,87, 87 into 87, unify on (0).2 in 87 and (0).2.1 in 87
  have eq142 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X0) ◇ (X2 ◇ X2)) := superpose eq86 eq97 -- forward demodulation 97,86
  have eq462 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq142 -- superposition 142,9, 9 into 142, unify on (0).2 in 9 and (0).2 in 142
  have eq774 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq462 eq10 -- superposition 10,462, 462 into 10, unify on (0).2 in 462 and (0).2.2 in 10
  subsumption eq774 rfl


@[equational_result]
theorem Equation3679_implies_Equation3665 (G : Type*) [Magma G] (h : Equation3679 G) : Equation3665 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = ((X3 ◇ X0) ◇ (X3 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq29 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) = (X2 ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq137 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ sK1) ◇ (X0 ◇ X1)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq464 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq14 eq137 -- superposition 137,14, 14 into 137, unify on (0).2 in 14 and (0).2 in 137
  subsumption eq464 eq29


@[equational_result]
theorem Equation3679_implies_Equation3661 (G : Type*) [Magma G] (h : Equation3679 G) : Equation3661 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X3 : G) : (X3 ◇ X3) = (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq20 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X1) = ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X2 ◇ X4)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq70 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) = ((X3 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X4)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2.1.2 in 12
  have eq72 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) = ((((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.1 in 9
  have eq83 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) := superpose eq20 eq70 -- forward demodulation 70,20
  have eq88 (X0 X2 X3 : G) : (X2 ◇ X2) = ((X2 ◇ X2) ◇ (X0 ◇ X3)) := superpose eq83 eq72 -- forward demodulation 72,83
  have eq285 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq88 eq10 -- superposition 10,88, 88 into 10, unify on (0).2 in 88 and (0).2 in 10
  subsumption eq285 rfl


@[equational_result]
theorem Equation3679_implies_Equation3693 (G : Type*) [Magma G] (h : Equation3679 G) : Equation3693 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X0 ◇ X3) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X0 X1 X3 : G) : (X3 ◇ X3) = (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq20 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X1) = ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X2 ◇ X4)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq70 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) = ((X3 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X4)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2.1.2 in 12
  have eq72 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) = ((((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.1 in 9
  have eq83 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) := superpose eq20 eq70 -- forward demodulation 70,20
  have eq88 (X0 X2 X3 : G) : (X2 ◇ X2) = ((X2 ◇ X2) ◇ (X0 ◇ X3)) := superpose eq83 eq72 -- forward demodulation 72,83
  have eq282 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq88 eq10 -- superposition 10,88, 88 into 10, unify on (0).2 in 88 and (0).2 in 10
  have eq504 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X1 ◇ X3) ◇ (X1 ◇ X3)) := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  have eq632 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq504 -- superposition 504,9, 9 into 504, unify on (0).2 in 9 and (0).2 in 504
  have eq931 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq632 eq282 -- superposition 282,632, 632 into 282, unify on (0).2 in 632 and (0).2 in 282
  subsumption eq931 eq632


@[equational_result]
theorem Equation3679_implies_Equation3698 (G : Type*) [Magma G] (h : Equation3679 G) : Equation3698 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = ((X3 ◇ X0) ◇ (X3 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq29 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) = (X2 ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq137 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ sK2) ◇ (X0 ◇ X1)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq464 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq14 eq137 -- superposition 137,14, 14 into 137, unify on (0).2 in 14 and (0).2 in 137
  subsumption eq464 eq29


@[equational_result]
theorem Equation3679_implies_Equation3701 (G : Type*) [Magma G] (h : Equation3679 G) : Equation3701 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = ((X3 ◇ X0) ◇ (X3 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq29 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) = (X2 ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq137 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ sK2) ◇ (X0 ◇ X1)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq464 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq14 eq137 -- superposition 137,14, 14 into 137, unify on (0).2 in 14 and (0).2 in 137
  subsumption eq464 eq29


@[equational_result]
theorem Equation2074_implies_Equation2046 (G : Type*) [Magma G] (h : Equation2074 G) : Equation2046 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq47 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation2074_implies_Equation2060 (G : Type*) [Magma G] (h : Equation2074 G) : Equation2060 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq47 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation2074_implies_Equation2082 (G : Type*) [Magma G] (h : Equation2074 G) : Equation2082 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK3 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq47 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation2074_implies_Equation2037 (G : Type*) [Magma G] (h : Equation2074 G) : Equation2037 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq47 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation2868_implies_Equation2646 (G : Type*) [Magma G] (h : Equation2868 G) : Equation2646 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X3 : G) : (((X0 ◇ X0) ◇ X3) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation2868_implies_Equation2652 (G : Type*) [Magma G] (h : Equation2868 G) : Equation2652 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X3 : G) : (((X0 ◇ X0) ◇ X3) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation2868_implies_Equation257 (G : Type*) [Magma G] (h : Equation2868 G) : Equation257 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X3 : G) : (((X0 ◇ X0) ◇ X3) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation2868_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2868 G) : Equation2644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X3 : G) : (((X0 ◇ X0) ◇ X3) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.2 in 8
  have eq15 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq15 rfl


@[equational_result]
theorem Equation848_implies_Equation835 (G : Type*) [Magma G] (h : Equation848 G) : Equation835 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X3) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ X0) = (((X3 ◇ X3) ◇ X0) ◇ ((X4 ◇ X4) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0)))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq19 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X4) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = (((X4 ◇ X4) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) ◇ ((X5 ◇ X5) ◇ ((X3 ◇ X3) ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq32 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X3 ◇ X3) ◇ ((X4 ◇ X4) ◇ (X5 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X0))))))) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1 in 17
  have eq92 (X0 X1 X4 X5 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X4 ◇ X4) ◇ ((X5 ◇ X5) ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq17 eq32 -- superposition 32,17, 17 into 32, unify on (0).2 in 17 and (0).2.2.2.2 in 32
  have eq134 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X3 ◇ X3) ◇ ((X4 ◇ X4) ◇ X1))) := superpose eq11 eq19 -- superposition 19,11, 11 into 19, unify on (0).2 in 11 and (0).1 in 19
  have eq1840 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq134 eq92 -- superposition 92,134, 134 into 92, unify on (0).2 in 134 and (0).2.2 in 92
  have eq1973 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq1840 eq9 -- superposition 9,1840, 1840 into 9, unify on (0).2 in 1840 and (0).1.2 in 9
  have eq2942 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X1 := superpose eq1973 eq9 -- superposition 9,1973, 1973 into 9, unify on (0).2 in 1973 and (0).1.2 in 9
  have eq3351 : sK0 ≠ sK0 := superpose eq2942 eq10 -- superposition 10,2942, 2942 into 10, unify on (0).2 in 2942 and (0).2 in 10
  subsumption eq3351 rfl


@[equational_result]
theorem Equation2304_implies_Equation817 (G : Type*) [Magma G] (h : Equation2304 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = ((X0 ◇ X1) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq13 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) = X1 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1 in 8
  have eq20 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq23 : sK0 ≠ sK0 := superpose eq20 eq9 -- superposition 9,20, 20 into 9, unify on (0).2 in 20 and (0).2 in 9
  subsumption eq23 rfl


@[equational_result]
theorem Equation556_implies_Equation4405 (G : Type*) [Magma G] (h : Equation556 G) : Equation4405 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation556_implies_Equation4442 (G : Type*) [Magma G] (h : Equation556 G) : Equation4442 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation556_implies_Equation4482 (G : Type*) [Magma G] (h : Equation556 G) : Equation4482 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation556_implies_Equation4531 (G : Type*) [Magma G] (h : Equation556 G) : Equation4531 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation556_implies_Equation43 (G : Type*) [Magma G] (h : Equation556 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation556_implies_Equation4435 (G : Type*) [Magma G] (h : Equation556 G) : Equation4435 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq14 -- forward demodulation 14,13
  subsumption eq16 rfl


@[equational_result]
theorem Equation556_implies_Equation4635 (G : Type*) [Magma G] (h : Equation556 G) : Equation4635 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq14 -- forward demodulation 14,13
  subsumption eq16 eq13


@[equational_result]
theorem Equation556_implies_Equation4677 (G : Type*) [Magma G] (h : Equation556 G) : Equation4677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK1 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : ((sK0 ◇ sK1) ◇ sK2) ≠ (sK2 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 : ((sK0 ◇ sK1) ◇ sK2) ≠ (sK2 ◇ (sK0 ◇ sK1)) := superpose eq13 eq14 -- forward demodulation 14,13
  subsumption eq16 eq13


@[equational_result]
theorem Equation1119_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1119 G) : Equation1223 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.2 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq19 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq20 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.2 in 11
  have eq21 (X0 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).1.1 in 10
  have eq22 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.2.1 in 8
  have eq27 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))))) := superpose eq10 eq19 -- forward demodulation 19,10
  have eq28 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq8 eq20 -- forward demodulation 20,8
  have eq29 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq28 eq27 -- backward demodulation 27,28
  have eq30 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq28 eq21 -- forward demodulation 21,28
  have eq31 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq28 eq22 -- forward demodulation 22,28
  have eq32 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq31 eq29 -- backward demodulation 29,31
  have eq34 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq30 eq32 -- forward demodulation 32,30
  have eq35 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq31 eq34 -- forward demodulation 34,31
  have eq72 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq35 eq31 -- superposition 31,35, 35 into 31, unify on (0).2 in 35 and (0).1.2 in 31
  have eq77 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := superpose eq72 eq9 -- backward demodulation 9,72
  have eq78 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq72 eq77 -- forward demodulation 77,72
  subsumption eq78 eq31


@[equational_result]
theorem Equation1119_implies_Equation359 (G : Type*) [Magma G] (h : Equation1119 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.2 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq19 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq20 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.2 in 11
  have eq21 (X0 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).1.1 in 10
  have eq22 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.2.1 in 8
  have eq27 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))))) := superpose eq10 eq19 -- forward demodulation 19,10
  have eq28 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq8 eq20 -- forward demodulation 20,8
  have eq29 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq28 eq27 -- backward demodulation 27,28
  have eq30 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq28 eq21 -- forward demodulation 21,28
  have eq31 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq28 eq22 -- forward demodulation 22,28
  have eq32 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq31 eq29 -- backward demodulation 29,31
  have eq34 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq30 eq32 -- forward demodulation 32,30
  have eq35 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq31 eq34 -- forward demodulation 34,31
  have eq72 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq35 eq31 -- superposition 31,35, 35 into 31, unify on (0).2 in 35 and (0).1.2 in 31
  have eq128 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq72 eq9 -- superposition 9,72, 72 into 9, unify on (0).2 in 72 and (0).2 in 9
  subsumption eq128 rfl


@[equational_result]
theorem Equation1119_implies_Equation2035 (G : Type*) [Magma G] (h : Equation1119 G) : Equation2035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.2 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq19 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq20 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.2 in 11
  have eq21 (X0 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).1.1 in 10
  have eq22 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.2.1 in 8
  have eq27 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))))) := superpose eq10 eq19 -- forward demodulation 19,10
  have eq28 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq8 eq20 -- forward demodulation 20,8
  have eq29 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq28 eq27 -- backward demodulation 27,28
  have eq30 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq28 eq21 -- forward demodulation 21,28
  have eq31 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq28 eq22 -- forward demodulation 22,28
  have eq32 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq31 eq29 -- backward demodulation 29,31
  have eq34 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq30 eq32 -- forward demodulation 32,30
  have eq35 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq31 eq34 -- forward demodulation 34,31
  have eq72 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq35 eq31 -- superposition 31,35, 35 into 31, unify on (0).2 in 35 and (0).1.2 in 31
  have eq77 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq72 eq9 -- backward demodulation 9,72
  subsumption eq77 eq35


@[equational_result]
theorem Equation1119_implies_Equation151 (G : Type*) [Magma G] (h : Equation1119 G) : Equation151 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.2 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq19 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq20 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.2 in 11
  have eq21 (X0 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).1.1 in 10
  have eq22 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.2.1 in 8
  have eq27 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))))) := superpose eq10 eq19 -- forward demodulation 19,10
  have eq28 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq8 eq20 -- forward demodulation 20,8
  have eq29 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq28 eq27 -- backward demodulation 27,28
  have eq30 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq28 eq21 -- forward demodulation 21,28
  have eq31 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq28 eq22 -- forward demodulation 22,28
  have eq32 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq31 eq29 -- backward demodulation 29,31
  have eq34 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq30 eq32 -- forward demodulation 32,30
  have eq35 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq31 eq34 -- forward demodulation 34,31
  have eq72 : sK0 ≠ sK0 := superpose eq35 eq9 -- superposition 9,35, 35 into 9, unify on (0).2 in 35 and (0).2 in 9
  subsumption eq72 rfl


@[equational_result]
theorem Equation1119_implies_Equation4065 (G : Type*) [Magma G] (h : Equation1119 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.2 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq19 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq20 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.2 in 11
  have eq21 (X0 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).1.1 in 10
  have eq22 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.2.1 in 8
  have eq27 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))))) := superpose eq10 eq19 -- forward demodulation 19,10
  have eq28 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq8 eq20 -- forward demodulation 20,8
  have eq29 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq28 eq27 -- backward demodulation 27,28
  have eq30 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq28 eq21 -- forward demodulation 21,28
  have eq31 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq28 eq22 -- forward demodulation 22,28
  have eq32 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq31 eq29 -- backward demodulation 29,31
  have eq34 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq30 eq32 -- forward demodulation 32,30
  have eq35 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq31 eq34 -- forward demodulation 34,31
  have eq72 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq35 eq31 -- superposition 31,35, 35 into 31, unify on (0).2 in 35 and (0).1.2 in 31
  have eq77 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq72 eq9 -- backward demodulation 9,72
  subsumption eq77 eq72


@[equational_result]
theorem Equation1119_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1119 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.2 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq19 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq20 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.2 in 11
  have eq21 (X0 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).1.1 in 10
  have eq22 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.2.1 in 8
  have eq27 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))))) := superpose eq10 eq19 -- forward demodulation 19,10
  have eq28 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq8 eq20 -- forward demodulation 20,8
  have eq29 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq28 eq27 -- backward demodulation 27,28
  have eq30 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq28 eq21 -- forward demodulation 21,28
  have eq31 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq28 eq22 -- forward demodulation 22,28
  have eq32 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq31 eq29 -- backward demodulation 29,31
  have eq34 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq30 eq32 -- forward demodulation 32,30
  have eq35 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq31 eq34 -- forward demodulation 34,31
  have eq72 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq35 eq31 -- superposition 31,35, 35 into 31, unify on (0).2 in 35 and (0).1.2 in 31
  have eq77 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq72 eq9 -- backward demodulation 9,72
  subsumption eq77 eq35


@[equational_result]
theorem Equation1119_implies_Equation99 (G : Type*) [Magma G] (h : Equation1119 G) : Equation99 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.2 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq19 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq20 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.2 in 11
  have eq21 (X0 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).1.1 in 10
  have eq22 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.2.1 in 8
  have eq27 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))))) := superpose eq10 eq19 -- forward demodulation 19,10
  have eq28 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq8 eq20 -- forward demodulation 20,8
  have eq29 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq28 eq27 -- backward demodulation 27,28
  have eq30 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq28 eq21 -- forward demodulation 21,28
  have eq31 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq28 eq22 -- forward demodulation 22,28
  have eq32 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq31 eq29 -- backward demodulation 29,31
  have eq34 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq30 eq32 -- forward demodulation 32,30
  have eq35 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq31 eq34 -- forward demodulation 34,31
  have eq72 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq35 eq31 -- superposition 31,35, 35 into 31, unify on (0).2 in 35 and (0).1.2 in 31
  have eq77 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq72 eq9 -- backward demodulation 9,72
  subsumption eq77 eq31


@[equational_result]
theorem Equation1670_implies_Equation2459 (G : Type*) [Magma G] (h : Equation1670 G) : Equation2459 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq109 : sK0 ≠ sK0 := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).2 in 10
  subsumption eq109 rfl


@[equational_result]
theorem Equation1670_implies_Equation3319 (G : Type*) [Magma G] (h : Equation1670 G) : Equation3319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 (X0 X1 X3 : G) : (X3 ◇ X1) = (X3 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.1 in 11
  have eq84 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq84 rfl


@[equational_result]
theorem Equation1670_implies_Equation2482 (G : Type*) [Magma G] (h : Equation1670 G) : Equation2482 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq109 : sK0 ≠ sK0 := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).2 in 10
  subsumption eq109 rfl


@[equational_result]
theorem Equation1670_implies_Equation3334 (G : Type*) [Magma G] (h : Equation1670 G) : Equation3334 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 (X0 X1 X3 : G) : (X3 ◇ X1) = (X3 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.1 in 11
  have eq84 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq84 rfl


@[equational_result]
theorem Equation109_implies_Equation1251 (G : Type*) [Magma G] (h : Equation109 G) : Equation1251 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq29 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation109_implies_Equation1253 (G : Type*) [Magma G] (h : Equation109 G) : Equation1253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq29 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation109_implies_Equation1252 (G : Type*) [Magma G] (h : Equation109 G) : Equation1252 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq29 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation109_implies_Equation1256 (G : Type*) [Magma G] (h : Equation109 G) : Equation1256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq29 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation109_implies_Equation1223 (G : Type*) [Magma G] (h : Equation109 G) : Equation1223 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq28 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq28 rfl


@[equational_result]
theorem Equation109_implies_Equation1224 (G : Type*) [Magma G] (h : Equation109 G) : Equation1224 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq29 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation109_implies_Equation1248 (G : Type*) [Magma G] (h : Equation109 G) : Equation1248 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq29 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation446_implies_Equation458 (G : Type*) [Magma G] (h : Equation446 G) : Equation458 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) = ((X3 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq35 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) = X2 := superpose eq20 eq9 -- superposition 9,20, 20 into 9, unify on (0).2 in 20 and (0).1.2 in 9
  have eq78 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq35 eq9 -- superposition 9,35, 35 into 9, unify on (0).2 in 35 and (0).1.2.2 in 9
  have eq222 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := superpose eq78 eq35 -- superposition 35,78, 78 into 35, unify on (0).2 in 78 and (0).1.2 in 35
  have eq338 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := superpose eq222 eq11 -- superposition 11,222, 222 into 11, unify on (0).2 in 222 and (0).1 in 11
  have eq501 : sK0 ≠ sK0 := superpose eq338 eq10 -- superposition 10,338, 338 into 10, unify on (0).2 in 338 and (0).2 in 10
  subsumption eq501 rfl


@[equational_result]
theorem Equation446_implies_Equation442 (G : Type*) [Magma G] (h : Equation446 G) : Equation442 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) = ((X3 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq35 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) = X2 := superpose eq20 eq9 -- superposition 9,20, 20 into 9, unify on (0).2 in 20 and (0).1.2 in 9
  have eq78 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq35 eq9 -- superposition 9,35, 35 into 9, unify on (0).2 in 35 and (0).1.2.2 in 9
  have eq222 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := superpose eq78 eq35 -- superposition 35,78, 78 into 35, unify on (0).2 in 78 and (0).1.2 in 35
  have eq338 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := superpose eq222 eq11 -- superposition 11,222, 222 into 11, unify on (0).2 in 222 and (0).1 in 11
  have eq501 : sK0 ≠ sK0 := superpose eq338 eq10 -- superposition 10,338, 338 into 10, unify on (0).2 in 338 and (0).2 in 10
  subsumption eq501 rfl


@[equational_result]
theorem Equation1586_implies_Equation4666 (G : Type*) [Magma G] (h : Equation1586 G) : Equation4666 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X2) ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2))) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1.2 in 11
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq82 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ X0)) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X0))) = X0 := superpose eq12 eq21 -- superposition 21,12, 12 into 21, unify on (0).2 in 12 and (0).1.2 in 21
  have eq511 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2))) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2)))) = ((X3 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X2) := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).2.2 in 12
  have eq557 (X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X5)) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X5))) = X5 := superpose eq9 eq82 -- superposition 82,9, 9 into 82, unify on (0).2 in 9 and (0).1.2.1 in 82
  have eq695 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2))) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2)))) = (X0 ◇ X2) := superpose eq14 eq17 -- superposition 17,14, 14 into 17, unify on (0).2 in 14 and (0).2.2 in 17
  have eq797 (X0 X2 X3 : G) : ((X3 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X2) = (X0 ◇ X2) := superpose eq695 eq511 -- backward demodulation 511,695
  have eq1247 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ X4) = ((X3 ◇ ((X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)))) ◇ X4) := superpose eq17 eq797 -- superposition 797,17, 17 into 797, unify on (0).2 in 17 and (0).1.1.2.1 in 797
  have eq1382 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ X4) = ((X3 ◇ X0) ◇ X4) := superpose eq557 eq1247 -- forward demodulation 1247,557
  have eq1617 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X1) = ((X3 ◇ X0) ◇ X1) := superpose eq1382 eq1382 -- superposition 1382,1382, 1382 into 1382, unify on (0).2 in 1382 and (0).1 in 1382
  have eq1844 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ sK1) := superpose eq1382 eq10 -- superposition 10,1382, 1382 into 10, unify on (0).2 in 1382 and (0).2 in 10
  subsumption eq1844 eq1617


@[equational_result]
theorem Equation1586_implies_Equation4689 (G : Type*) [Magma G] (h : Equation1586 G) : Equation4689 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK3 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X2) ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2))) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1.2 in 11
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq82 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ X0)) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X0))) = X0 := superpose eq12 eq21 -- superposition 21,12, 12 into 21, unify on (0).2 in 12 and (0).1.2 in 21
  have eq503 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2))) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2)))) = ((X3 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X2) := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).2.2 in 12
  have eq557 (X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X5)) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X5))) = X5 := superpose eq9 eq82 -- superposition 82,9, 9 into 82, unify on (0).2 in 9 and (0).1.2.1 in 82
  have eq695 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2))) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2)))) = (X0 ◇ X2) := superpose eq14 eq17 -- superposition 17,14, 14 into 17, unify on (0).2 in 14 and (0).2.2 in 17
  have eq797 (X0 X2 X3 : G) : ((X3 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X2) = (X0 ◇ X2) := superpose eq695 eq503 -- backward demodulation 503,695
  have eq1111 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ X4) = ((X3 ◇ ((X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)))) ◇ X4) := superpose eq17 eq797 -- superposition 797,17, 17 into 797, unify on (0).2 in 17 and (0).1.1.2.1 in 797
  have eq1228 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ X4) = ((X3 ◇ X0) ◇ X4) := superpose eq557 eq1111 -- forward demodulation 1111,557
  have eq1626 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X1) = ((X3 ◇ X0) ◇ X1) := superpose eq1228 eq1228 -- superposition 1228,1228, 1228 into 1228, unify on (0).2 in 1228 and (0).1 in 1228
  have eq1793 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK1 ◇ sK1) ◇ sK2) := superpose eq1228 eq10 -- superposition 10,1228, 1228 into 10, unify on (0).2 in 1228 and (0).2 in 10
  subsumption eq1793 eq1626


@[equational_result]
theorem Equation2241_implies_Equation4065 (G : Type*) [Magma G] (h : Equation2241 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1.2 in 10
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq8 eq13 -- forward demodulation 13,8
  have eq17 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.1 in 8
  have eq23 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq17 eq9 -- backward demodulation 9,17
  subsumption eq23 rfl


@[equational_result]
theorem Equation2241_implies_Equation23 (G : Type*) [Magma G] (h : Equation2241 G) : Equation23 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1.2 in 10
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq8 eq13 -- forward demodulation 13,8
  have eq17 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.1 in 8
  have eq27 : sK0 ≠ sK0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2 in 9
  subsumption eq27 rfl


@[equational_result]
theorem Equation2241_implies_Equation1426 (G : Type*) [Magma G] (h : Equation2241 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1.2 in 10
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq8 eq13 -- forward demodulation 13,8
  have eq21 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.1.2.2 in 8
  have eq24 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq15 eq21 -- forward demodulation 21,15
  have eq74 : sK0 ≠ sK0 := superpose eq24 eq9 -- superposition 9,24, 24 into 9, unify on (0).2 in 24 and (0).2 in 9
  subsumption eq74 rfl


@[equational_result]
theorem Equation2241_implies_Equation3253 (G : Type*) [Magma G] (h : Equation2241 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1.2 in 10
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq8 eq13 -- forward demodulation 13,8
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).2 in 9
  subsumption eq16 rfl


@[equational_result]
theorem Equation2241_implies_Equation1832 (G : Type*) [Magma G] (h : Equation2241 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1.2 in 10
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq8 eq13 -- forward demodulation 13,8
  have eq19 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.1.2 in 8
  have eq50 : sK0 ≠ sK0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2 in 9
  subsumption eq50 rfl


@[equational_result]
theorem Equation3103_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3103 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq9 -- backward demodulation 9,12
  subsumption eq13 rfl


@[equational_result]
theorem Equation3103_implies_Equation411 (G : Type*) [Magma G] (h : Equation3103 G) : Equation411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq9 -- backward demodulation 9,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3103_implies_Equation3915 (G : Type*) [Magma G] (h : Equation3103 G) : Equation3915 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq13 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 rfl


@[equational_result]
theorem Equation3103_implies_Equation1020 (G : Type*) [Magma G] (h : Equation3103 G) : Equation1020 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq9 -- backward demodulation 9,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3103_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3103 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq9 -- backward demodulation 9,12
  subsumption eq13 rfl


@[equational_result]
theorem Equation3103_implies_Equation3319 (G : Type*) [Magma G] (h : Equation3103 G) : Equation3319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq13 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 rfl


@[equational_result]
theorem Equation3103_implies_Equation1832 (G : Type*) [Magma G] (h : Equation3103 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq9 -- backward demodulation 9,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3103_implies_Equation1629 (G : Type*) [Magma G] (h : Equation3103 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq15 rfl


@[equational_result]
theorem Equation3103_implies_Equation8 (G : Type*) [Magma G] (h : Equation3103 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 : sK0 ≠ sK0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq13 rfl


@[equational_result]
theorem Equation3676_implies_Equation3709 (G : Type*) [Magma G] (h : Equation3676 G) : Equation3709 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq21 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2 in 9
  have eq29 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq39 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) = (((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq69 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.1 in 19
  have eq80 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).2.2 in 11
  have eq122 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq9 eq29 -- superposition 29,9, 9 into 29, unify on (0).2 in 9 and (0).1 in 29
  have eq146 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq69 eq122 -- forward demodulation 122,69
  have eq147 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq146 eq80 -- backward demodulation 80,146
  have eq148 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq147 eq19 -- backward demodulation 19,147
  have eq164 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq148 eq11 -- backward demodulation 11,148
  have eq185 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq164 eq22 -- backward demodulation 22,164
  have eq190 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq185 eq39 -- backward demodulation 39,185
  have eq191 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq190 eq12 -- backward demodulation 12,190
  have eq251 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq191 eq148 -- superposition 148,191, 191 into 148, unify on (0).2 in 191 and (0).2 in 148
  have eq302 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := superpose eq251 eq10 -- superposition 10,251, 251 into 10, unify on (0).2 in 251 and (0).2.2 in 10
  have eq640 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq302 -- superposition 302,9, 9 into 302, unify on (0).2 in 9 and (0).2 in 302
  subsumption eq640 eq251


@[equational_result]
theorem Equation3676_implies_Equation3687 (G : Type*) [Magma G] (h : Equation3676 G) : Equation3687 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq22 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq23 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2 in 9
  have eq30 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq36 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq20 -- superposition 20,9, 9 into 20, unify on (0).2 in 9 and (0).2.1 in 20
  have eq43 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq20 eq11 -- superposition 11,20, 20 into 11, unify on (0).2 in 20 and (0).2.2 in 11
  have eq77 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) = (((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq123 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).1 in 30
  have eq147 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq36 eq123 -- forward demodulation 123,36
  have eq148 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq147 eq43 -- backward demodulation 43,147
  have eq149 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq148 eq20 -- backward demodulation 20,148
  have eq165 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq149 eq11 -- backward demodulation 11,149
  have eq186 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq165 eq23 -- backward demodulation 23,165
  have eq191 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq186 eq77 -- backward demodulation 77,186
  have eq192 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq191 eq12 -- backward demodulation 12,191
  have eq241 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq192 eq149 -- superposition 149,192, 192 into 149, unify on (0).2 in 192 and (0).2 in 149
  have eq273 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq241 eq13 -- superposition 13,241, 241 into 13, unify on (0).2 in 241 and (0).2 in 13
  subsumption eq273 eq241


@[equational_result]
theorem Equation3676_implies_Equation3702 (G : Type*) [Magma G] (h : Equation3676 G) : Equation3702 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq22 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq23 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2 in 9
  have eq30 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq36 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq20 -- superposition 20,9, 9 into 20, unify on (0).2 in 9 and (0).2.1 in 20
  have eq43 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq20 eq11 -- superposition 11,20, 20 into 11, unify on (0).2 in 20 and (0).2.2 in 11
  have eq77 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) = (((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq123 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).1 in 30
  have eq147 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq36 eq123 -- forward demodulation 123,36
  have eq148 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq147 eq43 -- backward demodulation 43,147
  have eq149 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq148 eq20 -- backward demodulation 20,148
  have eq165 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq149 eq11 -- backward demodulation 11,149
  have eq186 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq165 eq23 -- backward demodulation 23,165
  have eq191 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq186 eq77 -- backward demodulation 77,186
  have eq192 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq191 eq12 -- backward demodulation 12,191
  have eq241 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq192 eq149 -- superposition 149,192, 192 into 149, unify on (0).2 in 192 and (0).2 in 149
  have eq283 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq241 eq13 -- superposition 13,241, 241 into 13, unify on (0).2 in 241 and (0).2 in 13
  subsumption eq283 eq241


@[equational_result]
theorem Equation3676_implies_Equation3665 (G : Type*) [Magma G] (h : Equation3676 G) : Equation3665 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq21 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq29 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq69 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.1 in 19
  have eq81 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).2.2 in 11
  have eq123 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq9 eq29 -- superposition 29,9, 9 into 29, unify on (0).2 in 9 and (0).1 in 29
  have eq147 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq69 eq123 -- forward demodulation 123,69
  have eq148 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq147 eq81 -- backward demodulation 81,147
  have eq149 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq148 eq19 -- backward demodulation 19,148
  have eq255 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq149 eq10 -- superposition 10,149, 149 into 10, unify on (0).2 in 149 and (0).2 in 10
  subsumption eq255 rfl


@[equational_result]
theorem Equation3676_implies_Equation3663 (G : Type*) [Magma G] (h : Equation3676 G) : Equation3663 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq21 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2 in 9
  have eq29 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq39 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) = (((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq69 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.1 in 19
  have eq80 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).2.2 in 11
  have eq122 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq9 eq29 -- superposition 29,9, 9 into 29, unify on (0).2 in 9 and (0).1 in 29
  have eq146 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq69 eq122 -- forward demodulation 122,69
  have eq147 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq146 eq80 -- backward demodulation 80,146
  have eq148 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq147 eq19 -- backward demodulation 19,147
  have eq164 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq148 eq11 -- backward demodulation 11,148
  have eq185 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq164 eq22 -- backward demodulation 22,164
  have eq190 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq185 eq39 -- backward demodulation 39,185
  have eq191 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq190 eq12 -- backward demodulation 12,190
  have eq251 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq191 eq148 -- superposition 148,191, 191 into 148, unify on (0).2 in 191 and (0).2 in 148
  have eq293 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq251 eq9 -- superposition 9,251, 251 into 9, unify on (0).2 in 251 and (0).2.1 in 9
  have eq302 (X0 : G) : (X0 ◇ X0) ≠ ((X0 ◇ X0) ◇ (sK1 ◇ sK2)) := superpose eq251 eq10 -- superposition 10,251, 251 into 10, unify on (0).2 in 251 and (0).1 in 10
  subsumption eq302 eq293


@[equational_result]
theorem Equation3676_implies_Equation40 (G : Type*) [Magma G] (h : Equation3676 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq21 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2 in 9
  have eq29 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq39 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) = (((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq69 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.1 in 19
  have eq80 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).2.2 in 11
  have eq122 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq9 eq29 -- superposition 29,9, 9 into 29, unify on (0).2 in 9 and (0).1 in 29
  have eq146 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq69 eq122 -- forward demodulation 122,69
  have eq147 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq146 eq80 -- backward demodulation 80,146
  have eq148 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq147 eq19 -- backward demodulation 19,147
  have eq164 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq148 eq11 -- backward demodulation 11,148
  have eq185 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq164 eq22 -- backward demodulation 22,164
  have eq190 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq185 eq39 -- backward demodulation 39,185
  have eq191 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq190 eq12 -- backward demodulation 12,190
  have eq251 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq191 eq148 -- superposition 148,191, 191 into 148, unify on (0).2 in 191 and (0).2 in 148
  have eq289 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq251 eq10 -- superposition 10,251, 251 into 10, unify on (0).2 in 251 and (0).2 in 10
  subsumption eq289 eq251


@[equational_result]
theorem Equation3676_implies_Equation3693 (G : Type*) [Magma G] (h : Equation3676 G) : Equation3693 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq21 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2 in 9
  have eq29 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq39 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) = (((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq69 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.1 in 19
  have eq80 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).2.2 in 11
  have eq122 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq9 eq29 -- superposition 29,9, 9 into 29, unify on (0).2 in 9 and (0).1 in 29
  have eq146 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq69 eq122 -- forward demodulation 122,69
  have eq147 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq146 eq80 -- backward demodulation 80,146
  have eq148 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq147 eq19 -- backward demodulation 19,147
  have eq164 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq148 eq11 -- backward demodulation 11,148
  have eq185 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq164 eq22 -- backward demodulation 22,164
  have eq190 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq185 eq39 -- backward demodulation 39,185
  have eq191 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq190 eq12 -- backward demodulation 12,190
  have eq251 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq191 eq148 -- superposition 148,191, 191 into 148, unify on (0).2 in 191 and (0).2 in 148
  have eq302 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (sK2 ◇ sK3)) := superpose eq251 eq10 -- superposition 10,251, 251 into 10, unify on (0).2 in 251 and (0).2.1 in 10
  have eq640 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq302 -- superposition 302,9, 9 into 302, unify on (0).2 in 9 and (0).2 in 302
  subsumption eq640 eq251


@[equational_result]
theorem Equation3676_implies_Equation3685 (G : Type*) [Magma G] (h : Equation3676 G) : Equation3685 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq21 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2 in 9
  have eq29 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq39 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) = (((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq69 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.1 in 19
  have eq87 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).2.2 in 11
  have eq122 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq9 eq29 -- superposition 29,9, 9 into 29, unify on (0).2 in 9 and (0).1 in 29
  have eq146 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq69 eq122 -- forward demodulation 122,69
  have eq147 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq146 eq87 -- backward demodulation 87,146
  have eq148 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq147 eq19 -- backward demodulation 19,147
  have eq164 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq148 eq11 -- backward demodulation 11,148
  have eq185 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq164 eq22 -- backward demodulation 22,164
  have eq190 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq185 eq39 -- backward demodulation 39,185
  have eq191 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq190 eq12 -- backward demodulation 12,190
  have eq251 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq191 eq148 -- superposition 148,191, 191 into 148, unify on (0).2 in 191 and (0).2 in 148
  have eq302 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (sK0 ◇ sK1)) := superpose eq251 eq10 -- superposition 10,251, 251 into 10, unify on (0).2 in 251 and (0).2.1 in 10
  have eq640 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq9 eq302 -- superposition 302,9, 9 into 302, unify on (0).2 in 9 and (0).2 in 302
  subsumption eq640 rfl


@[equational_result]
theorem Equation3676_implies_Equation3694 (G : Type*) [Magma G] (h : Equation3676 G) : Equation3694 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq21 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2 in 9
  have eq29 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq39 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) = (((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq69 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.1 in 19
  have eq80 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).2.2 in 11
  have eq122 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq9 eq29 -- superposition 29,9, 9 into 29, unify on (0).2 in 9 and (0).1 in 29
  have eq146 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq69 eq122 -- forward demodulation 122,69
  have eq147 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq146 eq80 -- backward demodulation 80,146
  have eq148 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq147 eq19 -- backward demodulation 19,147
  have eq164 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq148 eq11 -- backward demodulation 11,148
  have eq185 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq164 eq22 -- backward demodulation 22,164
  have eq190 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq185 eq39 -- backward demodulation 39,185
  have eq191 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq190 eq12 -- backward demodulation 12,190
  have eq251 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq191 eq148 -- superposition 148,191, 191 into 148, unify on (0).2 in 191 and (0).2 in 148
  have eq292 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq251 eq9 -- superposition 9,251, 251 into 9, unify on (0).2 in 251 and (0).2.2 in 9
  have eq302 (X0 : G) : (X0 ◇ X0) ≠ ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := superpose eq251 eq10 -- superposition 10,251, 251 into 10, unify on (0).2 in 251 and (0).1 in 10
  subsumption eq302 eq292


@[equational_result]
theorem Equation3676_implies_Equation3668 (G : Type*) [Magma G] (h : Equation3676 G) : Equation3668 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq22 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq23 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2 in 9
  have eq30 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq36 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq20 -- superposition 20,9, 9 into 20, unify on (0).2 in 9 and (0).2.1 in 20
  have eq47 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq20 eq11 -- superposition 11,20, 20 into 11, unify on (0).2 in 20 and (0).2.2 in 11
  have eq77 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) = (((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq123 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).1 in 30
  have eq147 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq36 eq123 -- forward demodulation 123,36
  have eq148 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq147 eq47 -- backward demodulation 47,147
  have eq149 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq148 eq20 -- backward demodulation 20,148
  have eq165 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq149 eq11 -- backward demodulation 11,149
  have eq186 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq165 eq23 -- backward demodulation 23,165
  have eq191 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq186 eq77 -- backward demodulation 77,186
  have eq192 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq191 eq12 -- backward demodulation 12,191
  have eq241 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq192 eq149 -- superposition 149,192, 192 into 149, unify on (0).2 in 192 and (0).2 in 149
  have eq283 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq241 eq13 -- superposition 13,241, 241 into 13, unify on (0).2 in 241 and (0).2 in 13
  subsumption eq283 eq241


@[equational_result]
theorem Equation3676_implies_Equation3669 (G : Type*) [Magma G] (h : Equation3676 G) : Equation3669 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq22 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq23 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2 in 9
  have eq30 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq36 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq20 -- superposition 20,9, 9 into 20, unify on (0).2 in 9 and (0).2.1 in 20
  have eq43 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq20 eq11 -- superposition 11,20, 20 into 11, unify on (0).2 in 20 and (0).2.2 in 11
  have eq77 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) = (((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq123 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).1 in 30
  have eq147 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq36 eq123 -- forward demodulation 123,36
  have eq148 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq147 eq43 -- backward demodulation 43,147
  have eq149 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq148 eq20 -- backward demodulation 20,148
  have eq165 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq149 eq11 -- backward demodulation 11,149
  have eq186 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq165 eq23 -- backward demodulation 23,165
  have eq191 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq186 eq77 -- backward demodulation 77,186
  have eq192 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq191 eq12 -- backward demodulation 12,191
  have eq241 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq192 eq149 -- superposition 149,192, 192 into 149, unify on (0).2 in 192 and (0).2 in 149
  have eq283 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq241 eq13 -- superposition 13,241, 241 into 13, unify on (0).2 in 241 and (0).2 in 13
  subsumption eq283 eq241


@[equational_result]
theorem Equation3676_implies_Equation3703 (G : Type*) [Magma G] (h : Equation3676 G) : Equation3703 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq22 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq23 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2 in 9
  have eq30 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq36 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq20 -- superposition 20,9, 9 into 20, unify on (0).2 in 9 and (0).2.1 in 20
  have eq43 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq20 eq11 -- superposition 11,20, 20 into 11, unify on (0).2 in 20 and (0).2.2 in 11
  have eq77 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) = (((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq123 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).1 in 30
  have eq147 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq36 eq123 -- forward demodulation 123,36
  have eq148 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq147 eq43 -- backward demodulation 43,147
  have eq149 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq148 eq20 -- backward demodulation 20,148
  have eq165 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq149 eq11 -- backward demodulation 11,149
  have eq186 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq165 eq23 -- backward demodulation 23,165
  have eq191 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq186 eq77 -- backward demodulation 77,186
  have eq192 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq191 eq12 -- backward demodulation 12,191
  have eq241 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq192 eq149 -- superposition 149,192, 192 into 149, unify on (0).2 in 192 and (0).2 in 149
  have eq283 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq241 eq13 -- superposition 13,241, 241 into 13, unify on (0).2 in 241 and (0).2 in 13
  subsumption eq283 eq241


@[equational_result]
theorem Equation3676_implies_Equation3705 (G : Type*) [Magma G] (h : Equation3676 G) : Equation3705 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq22 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq23 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2 in 9
  have eq30 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq36 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq20 -- superposition 20,9, 9 into 20, unify on (0).2 in 9 and (0).2.1 in 20
  have eq43 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq20 eq11 -- superposition 11,20, 20 into 11, unify on (0).2 in 20 and (0).2.2 in 11
  have eq77 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) = (((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq123 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).1 in 30
  have eq147 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq36 eq123 -- forward demodulation 123,36
  have eq148 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq147 eq43 -- backward demodulation 43,147
  have eq149 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq148 eq20 -- backward demodulation 20,148
  have eq165 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq149 eq11 -- backward demodulation 11,149
  have eq186 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq165 eq23 -- backward demodulation 23,165
  have eq191 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq186 eq77 -- backward demodulation 77,186
  have eq192 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq191 eq12 -- backward demodulation 12,191
  have eq241 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq192 eq149 -- superposition 149,192, 192 into 149, unify on (0).2 in 192 and (0).2 in 149
  have eq283 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq241 eq13 -- superposition 13,241, 241 into 13, unify on (0).2 in 241 and (0).2 in 13
  subsumption eq283 eq241


@[equational_result]
theorem Equation3502_implies_Equation4343 (G : Type*) [Magma G] (h : Equation3502 G) : Equation4343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X2) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq16 (X3 X4 X5 : G) : (X4 ◇ X4) = (X5 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq67 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq67 eq16


@[equational_result]
theorem Equation3502_implies_Equation3672 (G : Type*) [Magma G] (h : Equation3502 G) : Equation3672 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X2) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq16 (X3 X4 X5 : G) : (X4 ◇ X4) = (X5 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq31 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2.2 in 10
  subsumption eq31 eq16


@[equational_result]
theorem Equation3502_implies_Equation3303 (G : Type*) [Magma G] (h : Equation3502 G) : Equation3303 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X2) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3))) := mod_symm nh
  have eq16 (X3 X4 X5 : G) : (X4 ◇ X4) = (X5 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq67 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2 in 10
  subsumption eq67 eq16


@[equational_result]
theorem Equation3502_implies_Equation4355 (G : Type*) [Magma G] (h : Equation3502 G) : Equation4355 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X2) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq16 (X3 X4 X5 : G) : (X4 ◇ X4) = (X5 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq67 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq67 eq16


@[equational_result]
theorem Equation2052_implies_Equation3512 (G : Type*) [Magma G] (h : Equation2052 G) : Equation3512 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2052_implies_Equation3457 (G : Type*) [Magma G] (h : Equation2052 G) : Equation3457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2052_implies_Equation3513 (G : Type*) [Magma G] (h : Equation2052 G) : Equation3513 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2653_implies_Equation255 (G : Type*) [Magma G] (h : Equation2653 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1 in 8
  have eq16 : sK0 ≠ sK0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq16 rfl


@[equational_result]
theorem Equation2653_implies_Equation307 (G : Type*) [Magma G] (h : Equation2653 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1 in 8
  have eq13 (X0 X1 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X1 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1.2 in 8
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1.1 in 8
  have eq15 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq10 eq12 -- superposition 12,10, 10 into 12, unify on (0).2 in 10 and (0).1.1.1 in 12
  have eq21 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  have eq24 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq12 eq21 -- forward demodulation 21,12
  have eq25 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq24 eq11 -- backward demodulation 11,24
  have eq28 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq25 eq15 -- backward demodulation 15,25
  have eq32 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2 in 9
  subsumption eq32 rfl


@[equational_result]
theorem Equation2653_implies_Equation3456 (G : Type*) [Magma G] (h : Equation2653 G) : Equation3456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1 in 8
  have eq13 (X0 X1 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X1 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1.2 in 8
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1.1 in 8
  have eq15 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq10 eq12 -- superposition 12,10, 10 into 12, unify on (0).2 in 10 and (0).1.1.1 in 12
  have eq21 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  have eq24 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq12 eq21 -- forward demodulation 21,12
  have eq25 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq24 eq11 -- backward demodulation 11,24
  have eq28 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq25 eq15 -- backward demodulation 15,25
  have eq33 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq28 eq14 -- superposition 14,28, 28 into 14, unify on (0).2 in 28 and (0).2.1 in 14
  have eq35 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq24 eq33 -- forward demodulation 33,24
  have eq39 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq35 eq9 -- superposition 9,35, 35 into 9, unify on (0).2 in 35 and (0).2 in 9
  subsumption eq39 rfl


@[equational_result]
theorem Equation2653_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2653 G) : Equation2847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1 in 8
  have eq13 (X0 X1 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X1 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1.2 in 8
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1.1 in 8
  have eq19 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ X1) := superpose eq10 eq14 -- superposition 14,10, 10 into 14, unify on (0).2 in 10 and (0).1 in 14
  have eq21 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  have eq24 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq12 eq21 -- forward demodulation 21,12
  have eq25 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq24 eq11 -- backward demodulation 11,24
  have eq26 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := superpose eq25 eq19 -- backward demodulation 19,25
  have eq29 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq26 eq9 -- backward demodulation 9,26
  subsumption eq29 eq12


@[equational_result]
theorem Equation2653_implies_Equation2875 (G : Type*) [Magma G] (h : Equation2653 G) : Equation2875 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq13 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X1 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.1 in 9
  have eq20 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ X1) := superpose eq11 eq15 -- superposition 15,11, 11 into 15, unify on (0).2 in 11 and (0).1 in 15
  have eq22 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2.1 in 15
  have eq25 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq13 eq22 -- forward demodulation 22,13
  have eq26 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq25 eq12 -- backward demodulation 12,25
  have eq27 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose eq26 eq20 -- backward demodulation 20,26
  have eq30 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq27 eq10 -- backward demodulation 10,27
  subsumption eq30 eq13


@[equational_result]
theorem Equation2653_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2653 G) : Equation2035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1 in 8
  have eq13 (X0 X1 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X1 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1.2 in 8
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1.1 in 8
  have eq21 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  have eq24 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq12 eq21 -- forward demodulation 21,12
  have eq25 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq24 eq11 -- backward demodulation 11,24
  have eq37 : sK0 ≠ sK0 := superpose eq25 eq9 -- superposition 9,25, 25 into 9, unify on (0).2 in 25 and (0).2 in 9
  subsumption eq37 rfl


@[equational_result]
theorem Equation4549_implies_Equation4499 (G : Type*) [Magma G] (h : Equation4549 G) : Equation4499 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq37 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq51 (X1 : G) : ((sK2 ◇ sK2) ◇ sK2) ≠ (X1 ◇ (sK1 ◇ sK1)) := superpose eq9 eq37 -- superposition 37,9, 9 into 37, unify on (0).2 in 9 and (0).1 in 37
  have eq79 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ X0) = (X4 ◇ ((X3 ◇ X3) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq115 (X0 X1 : G) : ((sK2 ◇ sK2) ◇ sK2) ≠ (X1 ◇ ((sK1 ◇ sK1) ◇ X0)) := superpose eq9 eq51 -- superposition 51,9, 9 into 51, unify on (0).2 in 9 and (0).2 in 51
  subsumption eq115 eq79


@[equational_result]
theorem Equation4549_implies_Equation4527 (G : Type*) [Magma G] (h : Equation4549 G) : Equation4527 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (((X1 ◇ X1) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq40 (X0 X1 : G) : (X1 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq55 (X1 : G) : ((sK2 ◇ sK2) ◇ sK1) ≠ (X1 ◇ (sK0 ◇ sK1)) := superpose eq9 eq40 -- superposition 40,9, 9 into 40, unify on (0).2 in 9 and (0).2 in 40
  have eq77 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ X0) = (X5 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).2.2 in 13
  have eq292 (X0 X1 X2 : G) : ((sK2 ◇ sK2) ◇ sK1) ≠ (X2 ◇ ((sK0 ◇ sK1) ◇ (X1 ◇ X0))) := superpose eq14 eq55 -- superposition 55,14, 14 into 55, unify on (0).2 in 14 and (0).2 in 55
  subsumption eq292 eq77


@[equational_result]
theorem Equation4549_implies_Equation4471 (G : Type*) [Magma G] (h : Equation4549 G) : Equation4471 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq40 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq51 (X1 : G) : ((sK0 ◇ sK0) ◇ sK2) ≠ (X1 ◇ (sK1 ◇ sK1)) := superpose eq9 eq40 -- superposition 40,9, 9 into 40, unify on (0).2 in 9 and (0).1 in 40
  have eq79 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ X0) = (X4 ◇ ((X3 ◇ X3) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq115 (X0 X1 : G) : ((sK0 ◇ sK0) ◇ sK2) ≠ (X1 ◇ ((sK1 ◇ sK1) ◇ X0)) := superpose eq9 eq51 -- superposition 51,9, 9 into 51, unify on (0).2 in 9 and (0).2 in 51
  subsumption eq115 eq79


@[equational_result]
theorem Equation4549_implies_Equation4425 (G : Type*) [Magma G] (h : Equation4549 G) : Equation4425 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = (X3 ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq37 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK2)) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq55 (X1 : G) : ((sK1 ◇ sK1) ◇ sK0) ≠ (X1 ◇ (sK2 ◇ sK2)) := superpose eq9 eq37 -- superposition 37,9, 9 into 37, unify on (0).2 in 9 and (0).2 in 37
  have eq77 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ X0) = (X5 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).2.2 in 13
  have eq201 (X0 X1 X2 : G) : ((sK1 ◇ sK1) ◇ sK0) ≠ (X1 ◇ (X2 ◇ (X0 ◇ sK2))) := superpose eq12 eq55 -- superposition 55,12, 12 into 55, unify on (0).2 in 12 and (0).2 in 55
  subsumption eq201 eq77


@[equational_result]
theorem Equation4549_implies_Equation4397 (G : Type*) [Magma G] (h : Equation4549 G) : Equation4397 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (((X1 ◇ X1) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq40 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK0)) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq55 (X1 : G) : ((sK1 ◇ sK1) ◇ sK0) ≠ (X1 ◇ (sK2 ◇ sK0)) := superpose eq9 eq40 -- superposition 40,9, 9 into 40, unify on (0).2 in 9 and (0).2 in 40
  have eq77 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ X0) = (X5 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).2.2 in 13
  have eq294 (X0 X1 X2 : G) : ((sK1 ◇ sK1) ◇ sK0) ≠ (X2 ◇ ((sK2 ◇ sK0) ◇ (X1 ◇ X0))) := superpose eq14 eq55 -- superposition 55,14, 14 into 55, unify on (0).2 in 14 and (0).2 in 55
  subsumption eq294 eq77


@[equational_result]
theorem Equation4549_implies_Equation4509 (G : Type*) [Magma G] (h : Equation4549 G) : Equation4509 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK0) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (((X1 ◇ X1) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK3 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq40 (X0 X1 : G) : (X1 ◇ (sK3 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq55 (X1 : G) : ((sK2 ◇ sK2) ◇ sK1) ≠ (X1 ◇ (sK3 ◇ sK0)) := superpose eq9 eq40 -- superposition 40,9, 9 into 40, unify on (0).2 in 9 and (0).2 in 40
  have eq77 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ X0) = (X5 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).2.2 in 13
  have eq294 (X0 X1 X2 : G) : ((sK2 ◇ sK2) ◇ sK1) ≠ (X2 ◇ ((sK3 ◇ sK0) ◇ (X1 ◇ X0))) := superpose eq14 eq55 -- superposition 55,14, 14 into 55, unify on (0).2 in 14 and (0).2 in 55
  subsumption eq294 eq77


@[equational_result]
theorem Equation4549_implies_Equation4463 (G : Type*) [Magma G] (h : Equation4549 G) : Equation4463 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK2) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (((X1 ◇ X1) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK3 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq40 (X0 X1 : G) : (X1 ◇ (sK3 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK0)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq51 (X1 : G) : ((sK2 ◇ sK2) ◇ sK3) ≠ (X1 ◇ (sK1 ◇ sK0)) := superpose eq9 eq40 -- superposition 40,9, 9 into 40, unify on (0).2 in 9 and (0).1 in 40
  have eq77 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ X0) = (X5 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).2.2 in 13
  have eq292 (X0 X1 X2 : G) : ((sK2 ◇ sK2) ◇ sK3) ≠ (X2 ◇ ((sK1 ◇ sK0) ◇ (X1 ◇ X0))) := superpose eq14 eq51 -- superposition 51,14, 14 into 51, unify on (0).2 in 14 and (0).2 in 51
  subsumption eq292 eq77


@[equational_result]
theorem Equation4549_implies_Equation4500 (G : Type*) [Magma G] (h : Equation4549 G) : Equation4500 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK3 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq40 (X0 X1 : G) : (X1 ◇ (sK3 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq51 (X1 : G) : ((sK2 ◇ sK2) ◇ sK3) ≠ (X1 ◇ (sK1 ◇ sK1)) := superpose eq9 eq40 -- superposition 40,9, 9 into 40, unify on (0).2 in 9 and (0).1 in 40
  have eq79 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ X0) = (X4 ◇ ((X3 ◇ X3) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq115 (X0 X1 : G) : ((sK2 ◇ sK2) ◇ sK3) ≠ (X1 ◇ ((sK1 ◇ sK1) ◇ X0)) := superpose eq9 eq51 -- superposition 51,9, 9 into 51, unify on (0).2 in 9 and (0).2 in 51
  subsumption eq115 eq79


@[equational_result]
theorem Equation4549_implies_Equation4395 (G : Type*) [Magma G] (h : Equation4549 G) : Equation4395 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = (X3 ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK0 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq37 (X0 X1 : G) : (X1 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq55 (X1 : G) : ((sK1 ◇ sK1) ◇ sK0) ≠ (X1 ◇ (sK0 ◇ sK0)) := superpose eq9 eq37 -- superposition 37,9, 9 into 37, unify on (0).2 in 9 and (0).2 in 37
  have eq77 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ X0) = (X5 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).2.2 in 13
  have eq199 (X0 X1 X2 : G) : ((sK1 ◇ sK1) ◇ sK0) ≠ (X1 ◇ (X2 ◇ (X0 ◇ sK0))) := superpose eq12 eq55 -- superposition 55,12, 12 into 55, unify on (0).2 in 12 and (0).2 in 55
  subsumption eq199 eq77


@[equational_result]
theorem Equation4549_implies_Equation4389 (G : Type*) [Magma G] (h : Equation4549 G) : Equation4389 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq37 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK0 ◇ sK0)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq51 (X1 : G) : ((sK1 ◇ sK1) ◇ sK1) ≠ (X1 ◇ (sK0 ◇ sK0)) := superpose eq9 eq37 -- superposition 37,9, 9 into 37, unify on (0).2 in 9 and (0).1 in 37
  have eq79 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ X0) = (X4 ◇ ((X3 ◇ X3) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq115 (X0 X1 : G) : ((sK1 ◇ sK1) ◇ sK1) ≠ (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := superpose eq9 eq51 -- superposition 51,9, 9 into 51, unify on (0).2 in 9 and (0).2 in 51
  subsumption eq115 eq79


@[equational_result]
theorem Equation4549_implies_Equation4574 (G : Type*) [Magma G] (h : Equation4549 G) : Equation4574 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (((X1 ◇ X1) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK2 ◇ sK3)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq40 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK3)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq51 (X1 : G) : ((sK3 ◇ sK3) ◇ sK2) ≠ (X1 ◇ (sK1 ◇ sK2)) := superpose eq9 eq40 -- superposition 40,9, 9 into 40, unify on (0).2 in 9 and (0).1 in 40
  have eq77 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ X0) = (X5 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).2.2 in 13
  have eq292 (X0 X1 X2 : G) : ((sK3 ◇ sK3) ◇ sK2) ≠ (X2 ◇ ((sK1 ◇ sK2) ◇ (X1 ◇ X0))) := superpose eq14 eq51 -- superposition 51,14, 14 into 51, unify on (0).2 in 14 and (0).2 in 51
  subsumption eq292 eq77


@[equational_result]
theorem Equation4549_implies_Equation4507 (G : Type*) [Magma G] (h : Equation4549 G) : Equation4507 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (((X1 ◇ X1) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq40 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq55 (X1 : G) : ((sK2 ◇ sK2) ◇ sK1) ≠ (X1 ◇ (sK1 ◇ sK0)) := superpose eq9 eq40 -- superposition 40,9, 9 into 40, unify on (0).2 in 9 and (0).2 in 40
  have eq77 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ X0) = (X5 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).2.2 in 13
  have eq291 (X0 X1 X2 : G) : ((sK2 ◇ sK2) ◇ sK1) ≠ (X2 ◇ ((sK1 ◇ sK0) ◇ (X1 ◇ X0))) := superpose eq14 eq55 -- superposition 55,14, 14 into 55, unify on (0).2 in 14 and (0).2 in 55
  subsumption eq291 eq77


@[equational_result]
theorem Equation4549_implies_Equation4529 (G : Type*) [Magma G] (h : Equation4549 G) : Equation4529 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (((X1 ◇ X1) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK2 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq40 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq55 (X1 : G) : ((sK2 ◇ sK2) ◇ sK1) ≠ (X1 ◇ (sK2 ◇ sK1)) := superpose eq9 eq40 -- superposition 40,9, 9 into 40, unify on (0).2 in 9 and (0).2 in 40
  have eq77 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ X0) = (X5 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).2.2 in 13
  have eq294 (X0 X1 X2 : G) : ((sK2 ◇ sK2) ◇ sK1) ≠ (X2 ◇ ((sK2 ◇ sK1) ◇ (X1 ◇ X0))) := superpose eq14 eq55 -- superposition 55,14, 14 into 55, unify on (0).2 in 14 and (0).2 in 55
  subsumption eq294 eq77


@[equational_result]
theorem Equation4549_implies_Equation4576 (G : Type*) [Magma G] (h : Equation4549 G) : Equation4576 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK3) ◇ sK4) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (((X1 ◇ X1) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK4 ◇ sK3)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq40 (X0 X1 : G) : (X1 ◇ (sK4 ◇ sK3)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq51 (X1 : G) : ((sK3 ◇ sK3) ◇ sK4) ≠ (X1 ◇ (sK1 ◇ sK2)) := superpose eq9 eq40 -- superposition 40,9, 9 into 40, unify on (0).2 in 9 and (0).1 in 40
  have eq77 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ X0) = (X5 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).2.2 in 13
  have eq292 (X0 X1 X2 : G) : ((sK3 ◇ sK3) ◇ sK4) ≠ (X2 ◇ ((sK1 ◇ sK2) ◇ (X1 ◇ X0))) := superpose eq14 eq51 -- superposition 51,14, 14 into 51, unify on (0).2 in 14 and (0).2 in 51
  subsumption eq292 eq77


@[equational_result]
theorem Equation4549_implies_Equation4608 (G : Type*) [Magma G] (h : Equation4549 G) : Equation4608 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X0 X1 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ (X1 ◇ ((sK0 ◇ sK1) ◇ X0)) := superpose eq9 eq18 -- superposition 18,9, 9 into 18, unify on (0).2 in 9 and (0).2 in 18
  have eq76 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ X0) = (X5 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).2.2 in 13
  have eq194 (X0 X1 X2 X3 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq16 eq23 -- superposition 23,16, 16 into 23, unify on (0).2 in 16 and (0).2.2 in 23
  subsumption eq194 eq76


@[equational_result]
theorem Equation4549_implies_Equation4498 (G : Type*) [Magma G] (h : Equation4549 G) : Equation4498 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK2 ◇ sK2) ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).1 in 10
  have eq40 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq51 (X1 : G) : ((sK2 ◇ sK2) ◇ sK1) ≠ (X1 ◇ (sK1 ◇ sK1)) := superpose eq9 eq40 -- superposition 40,9, 9 into 40, unify on (0).2 in 9 and (0).1 in 40
  have eq79 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ X0) = (X4 ◇ ((X3 ◇ X3) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq115 (X0 X1 : G) : ((sK2 ◇ sK2) ◇ sK1) ≠ (X1 ◇ ((sK1 ◇ sK1) ◇ X0)) := superpose eq9 eq51 -- superposition 51,9, 9 into 51, unify on (0).2 in 9 and (0).2 in 51
  subsumption eq115 eq79


@[equational_result]
theorem Equation3896_implies_Equation3907 (G : Type*) [Magma G] (h : Equation3896 G) : Equation3907 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq27 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.1.2 in 9
  have eq29 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ (X0 ◇ X0)) ◇ sK2) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1.2 in 10
  subsumption eq29 eq27


@[equational_result]
theorem Equation3896_implies_Equation4623 (G : Type*) [Magma G] (h : Equation3896 G) : Equation4623 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ sK3) := mod_symm nh
  have eq15 (X3 X4 X5 : G) : (X4 ◇ X4) = ((X3 ◇ X3) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq56 (X0 : G) : (X0 ◇ X0) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq56 eq15


@[equational_result]
theorem Equation1461_implies_Equation4134 (G : Type*) [Magma G] (h : Equation1461 G) : Equation4134 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq33 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq20 eq11 -- superposition 11,20, 20 into 11, unify on (0).2 in 20 and (0).2.2 in 11
  have eq248 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = (X2 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq9 eq33 -- superposition 33,9, 9 into 33, unify on (0).2 in 9 and (0).2.2.2 in 33
  have eq376 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq248 -- superposition 248,12, 12 into 248, unify on (0).2 in 12 and (0).2.2 in 248
  have eq409 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq376 -- forward demodulation 376,9
  have eq902 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq409 eq9 -- superposition 9,409, 409 into 9, unify on (0).2 in 409 and (0).1.2 in 9
  have eq1153 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq902 eq10 -- superposition 10,902, 902 into 10, unify on (0).2 in 902 and (0).2 in 10
  subsumption eq1153 rfl


