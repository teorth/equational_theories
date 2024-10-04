import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation2338_implies_Equation3050 (G : Type*) [Magma G] (h : Equation2338 G) : Equation3050 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq11 (X0 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq18 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.1.2 in 8
  have eq20 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.1.2.2 in 8
  have eq21 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := superpose eq20 eq21 -- backward demodulation 21,20
  subsumption eq22 eq8


@[equational_result]
theorem Equation2338_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2338 G) : Equation2847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq11 (X0 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq20 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.1.2.2 in 8
  have eq21 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := superpose eq20 eq9 -- backward demodulation 9,20
  subsumption eq21 eq8


@[equational_result]
theorem Equation2338_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2338 G) : Equation2441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq11 (X0 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq18 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.1.2 in 8
  have eq21 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := superpose eq18 eq9 -- backward demodulation 9,18
  subsumption eq21 eq8


@[equational_result]
theorem Equation2338_implies_Equation411 (G : Type*) [Magma G] (h : Equation2338 G) : Equation411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq11 (X0 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq16 : sK0 ≠ sK0 := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).2 in 9
  subsumption eq16 rfl


@[equational_result]
theorem Equation3504_implies_Equation3664 (G : Type*) [Magma G] (h : Equation3504 G) : Equation3664 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X3) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X1)) = (X4 ◇ ((X5 ◇ X6) ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq23 (X0 : G) : (X0 ◇ X0) ≠ ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).1 in 10
  have eq39 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X0 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X2))) = (X5 ◇ ((X6 ◇ X7) ◇ X5)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq69 (X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X1)) ≠ ((sK0 ◇ sK1) ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) := superpose eq9 eq23 -- superposition 23,9, 9 into 23, unify on (0).2 in 9 and (0).1 in 23
  subsumption eq69 eq39


@[equational_result]
theorem Equation3504_implies_Equation3668 (G : Type*) [Magma G] (h : Equation3504 G) : Equation3668 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X3) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq25 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X0 ◇ X1) ◇ (X2 ◇ X2)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2 in 10
  subsumption eq26 eq25


@[equational_result]
theorem Equation3504_implies_Equation3674 (G : Type*) [Magma G] (h : Equation3504 G) : Equation3674 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X3) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq25 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X0 ◇ X1) ◇ (X2 ◇ X2)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq26 (X0 : G) : (X0 ◇ X0) ≠ ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).1 in 10
  subsumption eq26 eq25


@[equational_result]
theorem Equation3504_implies_Equation3678 (G : Type*) [Magma G] (h : Equation3504 G) : Equation3678 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X3) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ X5) = ((X0 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq23 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2 in 10
  have eq69 (X1 X2 X3 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) := superpose eq9 eq23 -- superposition 23,9, 9 into 23, unify on (0).2 in 9 and (0).2.2 in 23
  subsumption eq69 eq14


@[equational_result]
theorem Equation3504_implies_Equation3672 (G : Type*) [Magma G] (h : Equation3504 G) : Equation3672 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X3) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq25 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X3 ◇ X3) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2 in 10
  subsumption eq26 eq25


@[equational_result]
theorem Equation3504_implies_Equation3709 (G : Type*) [Magma G] (h : Equation3504 G) : Equation3709 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X3) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq16 (X3 X4 : G) : (X3 ◇ X3) = (X4 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq25 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X0 ◇ X1) ◇ (X2 ◇ X2)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2 in 10
  subsumption eq26 eq25


@[equational_result]
theorem Equation432_implies_Equation4131 (G : Type*) [Magma G] (h : Equation432 G) : Equation4131 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation432_implies_Equation4065 (G : Type*) [Magma G] (h : Equation432 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq11


@[equational_result]
theorem Equation432_implies_Equation378 (G : Type*) [Magma G] (h : Equation432 G) : Equation378 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation834_implies_Equation104 (G : Type*) [Magma G] (h : Equation834 G) : Equation104 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation834_implies_Equation1228 (G : Type*) [Magma G] (h : Equation834 G) : Equation1228 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation834_implies_Equation1248 (G : Type*) [Magma G] (h : Equation834 G) : Equation1248 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation2712_implies_Equation3306 (G : Type*) [Magma G] (h : Equation2712 G) : Equation3306 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq17 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq38 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X1) = X1 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.1.2 in 9
  have eq107 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.1 in 38
  have eq123 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq107 eq10 -- backward demodulation 10,107
  subsumption eq123 eq107


@[equational_result]
theorem Equation2712_implies_Equation2443 (G : Type*) [Magma G] (h : Equation2712 G) : Equation2443 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq17 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq39 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.1.1 in 9
  have eq243 : sK0 ≠ sK0 := superpose eq39 eq10 -- superposition 10,39, 39 into 10, unify on (0).2 in 39 and (0).2 in 10
  subsumption eq243 rfl


@[equational_result]
theorem Equation2712_implies_Equation2446 (G : Type*) [Magma G] (h : Equation2712 G) : Equation2446 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq17 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq33 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1.1.2 in 11
  have eq69 : sK0 ≠ sK0 := superpose eq33 eq10 -- superposition 10,33, 33 into 10, unify on (0).2 in 33 and (0).2 in 10
  subsumption eq69 rfl


@[equational_result]
theorem Equation2712_implies_Equation2456 (G : Type*) [Magma G] (h : Equation2712 G) : Equation2456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq17 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq39 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1.1.2 in 11
  have eq77 : sK0 ≠ sK0 := superpose eq39 eq10 -- superposition 10,39, 39 into 10, unify on (0).2 in 39 and (0).2 in 10
  subsumption eq77 rfl


@[equational_result]
theorem Equation2712_implies_Equation2466 (G : Type*) [Magma G] (h : Equation2712 G) : Equation2466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq17 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq33 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1.1.2 in 11
  have eq69 : sK0 ≠ sK0 := superpose eq33 eq10 -- superposition 10,33, 33 into 10, unify on (0).2 in 33 and (0).2 in 10
  subsumption eq69 rfl


@[equational_result]
theorem Equation2712_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2712 G) : Equation2238 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq16 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq32 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).1.1.2 in 10
  have eq37 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X1) = X1 := superpose eq16 eq8 -- superposition 8,16, 16 into 8, unify on (0).2 in 16 and (0).1.1.2 in 8
  have eq106 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq8 eq37 -- superposition 37,8, 8 into 37, unify on (0).2 in 8 and (0).1.1 in 37
  have eq122 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq106 eq9 -- backward demodulation 9,106
  subsumption eq122 eq32


@[equational_result]
theorem Equation2712_implies_Equation307 (G : Type*) [Magma G] (h : Equation2712 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq16 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq37 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X1) = X1 := superpose eq16 eq8 -- superposition 8,16, 16 into 8, unify on (0).2 in 16 and (0).1.1.2 in 8
  have eq106 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq8 eq37 -- superposition 37,8, 8 into 37, unify on (0).2 in 8 and (0).1.1 in 37
  have eq167 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq106 eq9 -- superposition 9,106, 106 into 9, unify on (0).2 in 106 and (0).2 in 9
  subsumption eq167 rfl


@[equational_result]
theorem Equation2712_implies_Equation323 (G : Type*) [Magma G] (h : Equation2712 G) : Equation323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq17 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq38 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X1) = X1 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.1.2 in 9
  have eq107 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.1 in 38
  have eq168 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq107 eq10 -- superposition 10,107, 107 into 10, unify on (0).2 in 107 and (0).2 in 10
  subsumption eq168 rfl


@[equational_result]
theorem Equation2712_implies_Equation2243 (G : Type*) [Magma G] (h : Equation2712 G) : Equation2243 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq17 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq33 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1.1.2 in 11
  have eq38 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X1) = X1 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.1.2 in 9
  have eq107 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.1 in 38
  have eq123 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq107 eq10 -- backward demodulation 10,107
  subsumption eq123 eq33


@[equational_result]
theorem Equation2712_implies_Equation2263 (G : Type*) [Magma G] (h : Equation2712 G) : Equation2263 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq17 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq33 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1.1.2 in 11
  have eq38 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X1) = X1 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.1.2 in 9
  have eq107 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.1 in 38
  have eq123 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq107 eq10 -- backward demodulation 10,107
  subsumption eq123 eq33


@[equational_result]
theorem Equation2712_implies_Equation2476 (G : Type*) [Magma G] (h : Equation2712 G) : Equation2476 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq17 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq33 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1.1.2 in 11
  have eq69 : sK0 ≠ sK0 := superpose eq33 eq10 -- superposition 10,33, 33 into 10, unify on (0).2 in 33 and (0).2 in 10
  subsumption eq69 rfl


@[equational_result]
theorem Equation2712_implies_Equation3142 (G : Type*) [Magma G] (h : Equation2712 G) : Equation3142 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq17 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq38 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X1) = X1 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.1.2 in 9
  have eq110 : sK0 ≠ sK0 := superpose eq38 eq10 -- superposition 10,38, 38 into 10, unify on (0).2 in 38 and (0).2 in 10
  subsumption eq110 rfl


@[equational_result]
theorem Equation3059_implies_Equation3078 (G : Type*) [Magma G] (h : Equation3059 G) : Equation3078 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.1 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq16 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq17 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq11 eq16 -- forward demodulation 16,11
  have eq19 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq17 eq13 -- superposition 13,17, 17 into 13, unify on (0).2 in 17 and (0).2.2 in 13
  have eq20 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.1.1 in 12
  have eq27 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq19 eq17 -- backward demodulation 17,19
  have eq30 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose eq20 eq27 -- backward demodulation 27,20
  have eq66 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq30 eq9 -- superposition 9,30, 30 into 9, unify on (0).2 in 30 and (0).1.1.1.1 in 9
  have eq73 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq66 eq10 -- backward demodulation 10,66
  subsumption eq73 eq9


@[equational_result]
theorem Equation3059_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3059 G) : Equation3456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1.1 in 8
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1 in 8
  have eq15 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq12 eq8 -- superposition 8,12, 12 into 8, unify on (0).2 in 12 and (0).1.1.1 in 8
  have eq16 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq10 eq15 -- forward demodulation 15,10
  have eq19 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).1.1.1 in 11
  have eq32 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq19 eq12 -- backward demodulation 12,19
  have eq39 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq32 eq9 -- superposition 9,32, 32 into 9, unify on (0).2 in 32 and (0).2 in 9
  subsumption eq39 rfl


@[equational_result]
theorem Equation2294_implies_Equation255 (G : Type*) [Magma G] (h : Equation2294 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq13 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1.2 in 10
  have eq18 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.1 in 8
  have eq23 : sK0 ≠ sK0 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).2 in 9
  subsumption eq23 rfl


@[equational_result]
theorem Equation1041_implies_Equation104 (G : Type*) [Magma G] (h : Equation1041 G) : Equation104 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1041_implies_Equation1228 (G : Type*) [Magma G] (h : Equation1041 G) : Equation1228 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation635_implies_Equation842 (G : Type*) [Magma G] (h : Equation635 G) : Equation842 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation635_implies_Equation832 (G : Type*) [Magma G] (h : Equation635 G) : Equation832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation635_implies_Equation822 (G : Type*) [Magma G] (h : Equation635 G) : Equation822 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation635_implies_Equation852 (G : Type*) [Magma G] (h : Equation635 G) : Equation852 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation2994_implies_Equation255 (G : Type*) [Magma G] (h : Equation2994 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X2 X3 : G) : (((X2 ◇ X2) ◇ X2) ◇ X3) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.2 in 8
  have eq16 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq16 rfl


@[equational_result]
theorem Equation2994_implies_Equation283 (G : Type*) [Magma G] (h : Equation2994 G) : Equation283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : (((X2 ◇ X2) ◇ X2) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation3869_implies_Equation3872 (G : Type*) [Magma G] (h : Equation3869 G) : Equation3872 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X2) = ((X2 ◇ (X0 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq36 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq36 rfl


@[equational_result]
theorem Equation3869_implies_Equation3871 (G : Type*) [Magma G] (h : Equation3869 G) : Equation3871 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X2) = ((X2 ◇ (X0 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq36 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq36 rfl


@[equational_result]
theorem Equation2054_implies_Equation307 (G : Type*) [Magma G] (h : Equation2054 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation2724_implies_Equation211 (G : Type*) [Magma G] (h : Equation2724 G) : Equation211 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X3 : G) : ((X1 ◇ (X3 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation280_implies_Equation3659 (G : Type*) [Magma G] (h : Equation280 G) : Equation3659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation162_implies_Equation3316 (G : Type*) [Magma G] (h : Equation162 G) : Equation3316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation3417_implies_Equation4398 (G : Type*) [Magma G] (h : Equation3417 G) : Equation4398 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X1 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq22 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  have eq25 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq57 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).2 in 25
  have eq63 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq57 eq22 -- backward demodulation 22,57
  subsumption eq63 rfl


@[equational_result]
theorem Equation3417_implies_Equation4358 (G : Type*) [Magma G] (h : Equation3417 G) : Equation4358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X1 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq56 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq9 eq22 -- superposition 22,9, 9 into 22, unify on (0).2 in 9 and (0).2 in 22
  have eq62 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq56 eq10 -- backward demodulation 10,56
  subsumption eq62 rfl


@[equational_result]
theorem Equation3417_implies_Equation4635 (G : Type*) [Magma G] (h : Equation3417 G) : Equation4635 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X1 ◇ X0))) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq14 : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq25 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq12 eq14 -- superposition 14,12, 12 into 14, unify on (0).2 in 12 and (0).1 in 14
  have eq26 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq58 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq9 eq26 -- superposition 26,9, 9 into 26, unify on (0).2 in 9 and (0).2 in 26
  have eq64 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq58 eq25 -- backward demodulation 25,58
  subsumption eq64 rfl


@[equational_result]
theorem Equation3417_implies_Equation43 (G : Type*) [Magma G] (h : Equation3417 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X1 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq24 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq56 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq9 eq24 -- superposition 24,9, 9 into 24, unify on (0).2 in 9 and (0).2 in 24
  have eq122 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq56 eq10 -- superposition 10,56, 56 into 10, unify on (0).2 in 56 and (0).2 in 10
  subsumption eq122 rfl


@[equational_result]
theorem Equation1033_implies_Equation825 (G : Type*) [Magma G] (h : Equation1033 G) : Equation825 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1))) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1.2 in 9
  have eq54 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq54 rfl


@[equational_result]
theorem Equation1033_implies_Equation827 (G : Type*) [Magma G] (h : Equation1033 G) : Equation827 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1))) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1.2 in 9
  have eq54 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq54 rfl


@[equational_result]
theorem Equation1255_implies_Equation1224 (G : Type*) [Magma G] (h : Equation1255 G) : Equation1224 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq20 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1.1 in 9
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) = X1 := superpose eq12 eq20 -- forward demodulation 20,12
  have eq61 : sK0 ≠ sK0 := superpose eq25 eq10 -- superposition 10,25, 25 into 10, unify on (0).2 in 25 and (0).2 in 10
  subsumption eq61 rfl


@[equational_result]
theorem Equation1255_implies_Equation1251 (G : Type*) [Magma G] (h : Equation1255 G) : Equation1251 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq20 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1.1 in 9
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) = X1 := superpose eq12 eq20 -- forward demodulation 20,12
  have eq61 : sK0 ≠ sK0 := superpose eq25 eq10 -- superposition 10,25, 25 into 10, unify on (0).2 in 25 and (0).2 in 10
  subsumption eq61 rfl


@[equational_result]
theorem Equation1255_implies_Equation1253 (G : Type*) [Magma G] (h : Equation1255 G) : Equation1253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq20 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1.1 in 9
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) = X1 := superpose eq12 eq20 -- forward demodulation 20,12
  have eq61 : sK0 ≠ sK0 := superpose eq25 eq10 -- superposition 10,25, 25 into 10, unify on (0).2 in 25 and (0).2 in 10
  subsumption eq61 rfl


@[equational_result]
theorem Equation2482_implies_Equation3261 (G : Type*) [Magma G] (h : Equation2482 G) : Equation3261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1)))) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq32 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X3)))) ◇ X1)) = (X0 ◇ X4) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq33 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X4)))) ◇ X2)))) = (X0 ◇ X5) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq42 (X0 X1 X5 : G) : (X0 ◇ X5) = (X0 ◇ (X1 ◇ (X1 ◇ X5))) := superpose eq32 eq33 -- forward demodulation 33,32
  have eq70 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq42 eq10 -- superposition 10,42, 42 into 10, unify on (0).2 in 42 and (0).2 in 10
  subsumption eq70 rfl


@[equational_result]
theorem Equation52_implies_Equation629 (G : Type*) [Magma G] (h : Equation52 G) : Equation629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq12 eq9


@[equational_result]
theorem Equation52_implies_Equation614 (G : Type*) [Magma G] (h : Equation52 G) : Equation614 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq11 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq10 eq9 -- backward demodulation 9,10
  subsumption eq11 eq8


@[equational_result]
theorem Equation52_implies_Equation359 (G : Type*) [Magma G] (h : Equation52 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq11 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq11 rfl


@[equational_result]
theorem Equation335_implies_Equation3456 (G : Type*) [Magma G] (h : Equation335 G) : Equation3456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.2 in 8
  have eq11 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq10 eq9 -- backward demodulation 9,10
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq8 eq11 -- forward demodulation 11,8
  subsumption eq12 eq8


@[equational_result]
theorem Equation335_implies_Equation3862 (G : Type*) [Magma G] (h : Equation335 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq8 eq9 -- forward demodulation 9,8
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.2 in 8
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 eq8


@[equational_result]
theorem Equation335_implies_Equation3659 (G : Type*) [Magma G] (h : Equation335 G) : Equation3659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.2 in 8
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).2.2 in 8
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq8 eq13 -- forward demodulation 13,8
  have eq23 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq8 eq16 -- superposition 16,8, 8 into 16, unify on (0).2 in 8 and (0).2.2 in 16
  have eq40 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq23 eq9 -- superposition 9,23, 23 into 9, unify on (0).2 in 23 and (0).2 in 9
  subsumption eq40 rfl


@[equational_result]
theorem Equation3573_implies_Equation4435 (G : Type*) [Magma G] (h : Equation3573 G) : Equation4435 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (X3 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq45 (X0 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq26 -- forward demodulation 26,9
  have eq85 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq45 -- superposition 45,9, 9 into 45, unify on (0).2 in 9 and (0).1 in 45
  have eq98 (X0 X1 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X1)) = (X3 ◇ X1) := superpose eq9 eq85 -- forward demodulation 85,9
  have eq352 (X0 X2 : G) : (X2 ◇ X0) = (X0 ◇ X2) := superpose eq9 eq98 -- superposition 98,9, 9 into 98, unify on (0).2 in 9 and (0).1 in 98
  have eq397 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq352 eq10 -- backward demodulation 10,352
  have eq398 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq352 eq397 -- forward demodulation 397,352
  subsumption eq398 rfl


@[equational_result]
theorem Equation3573_implies_Equation4544 (G : Type*) [Magma G] (h : Equation3573 G) : Equation4544 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (X3 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq45 (X0 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq26 -- forward demodulation 26,9
  have eq85 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq45 -- superposition 45,9, 9 into 45, unify on (0).2 in 9 and (0).1 in 45
  have eq98 (X0 X1 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X1)) = (X3 ◇ X1) := superpose eq9 eq85 -- forward demodulation 85,9
  have eq352 (X0 X2 : G) : (X2 ◇ X0) = (X0 ◇ X2) := superpose eq9 eq98 -- superposition 98,9, 9 into 98, unify on (0).2 in 9 and (0).1 in 98
  have eq397 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK2) ◇ sK0) := superpose eq352 eq10 -- backward demodulation 10,352
  subsumption eq397 eq352


@[equational_result]
theorem Equation3573_implies_Equation4635 (G : Type*) [Magma G] (h : Equation3573 G) : Equation4635 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (X3 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq45 (X0 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq26 -- forward demodulation 26,9
  have eq85 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq45 -- superposition 45,9, 9 into 45, unify on (0).2 in 9 and (0).1 in 45
  have eq98 (X0 X1 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X1)) = (X3 ◇ X1) := superpose eq9 eq85 -- forward demodulation 85,9
  have eq352 (X0 X2 : G) : (X2 ◇ X0) = (X0 ◇ X2) := superpose eq9 eq98 -- superposition 98,9, 9 into 98, unify on (0).2 in 9 and (0).1 in 98
  have eq397 : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq352 eq10 -- backward demodulation 10,352
  have eq398 : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq352 eq397 -- forward demodulation 397,352
  subsumption eq398 eq352


@[equational_result]
theorem Equation3573_implies_Equation4442 (G : Type*) [Magma G] (h : Equation3573 G) : Equation4442 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (X3 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq45 (X0 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq26 -- forward demodulation 26,9
  have eq85 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq45 -- superposition 45,9, 9 into 45, unify on (0).2 in 9 and (0).1 in 45
  have eq98 (X0 X1 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X1)) = (X3 ◇ X1) := superpose eq9 eq85 -- forward demodulation 85,9
  have eq352 (X0 X2 : G) : (X2 ◇ X0) = (X0 ◇ X2) := superpose eq9 eq98 -- superposition 98,9, 9 into 98, unify on (0).2 in 9 and (0).1 in 98
  have eq397 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq352 eq10 -- backward demodulation 10,352
  subsumption eq397 eq352


@[equational_result]
theorem Equation3573_implies_Equation4398 (G : Type*) [Magma G] (h : Equation3573 G) : Equation4398 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (X3 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq45 (X0 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq26 -- forward demodulation 26,9
  have eq85 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq45 -- superposition 45,9, 9 into 45, unify on (0).2 in 9 and (0).1 in 45
  have eq98 (X0 X1 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X1)) = (X3 ◇ X1) := superpose eq9 eq85 -- forward demodulation 85,9
  have eq352 (X0 X2 : G) : (X2 ◇ X0) = (X0 ◇ X2) := superpose eq9 eq98 -- superposition 98,9, 9 into 98, unify on (0).2 in 9 and (0).1 in 98
  have eq594 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq352 eq10 -- superposition 10,352, 352 into 10, unify on (0).2 in 352 and (0).2 in 10
  subsumption eq594 rfl


@[equational_result]
theorem Equation3573_implies_Equation4283 (G : Type*) [Magma G] (h : Equation3573 G) : Equation4283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (X3 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq45 (X0 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq26 -- forward demodulation 26,9
  have eq85 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq45 -- superposition 45,9, 9 into 45, unify on (0).2 in 9 and (0).1 in 45
  have eq98 (X0 X1 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X1)) = (X3 ◇ X1) := superpose eq9 eq85 -- forward demodulation 85,9
  have eq352 (X0 X2 : G) : (X2 ◇ X0) = (X0 ◇ X2) := superpose eq9 eq98 -- superposition 98,9, 9 into 98, unify on (0).2 in 9 and (0).1 in 98
  have eq397 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq352 eq10 -- backward demodulation 10,352
  subsumption eq397 rfl


@[equational_result]
theorem Equation3573_implies_Equation4677 (G : Type*) [Magma G] (h : Equation3573 G) : Equation4677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK1 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (X3 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq45 (X0 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq26 -- forward demodulation 26,9
  have eq85 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq45 -- superposition 45,9, 9 into 45, unify on (0).2 in 9 and (0).1 in 45
  have eq98 (X0 X1 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X1)) = (X3 ◇ X1) := superpose eq9 eq85 -- forward demodulation 85,9
  have eq352 (X0 X2 : G) : (X2 ◇ X0) = (X0 ◇ X2) := superpose eq9 eq98 -- superposition 98,9, 9 into 98, unify on (0).2 in 9 and (0).1 in 98
  have eq397 : ((sK0 ◇ sK1) ◇ sK2) ≠ (sK2 ◇ (sK1 ◇ sK0)) := superpose eq352 eq10 -- backward demodulation 10,352
  have eq398 : ((sK0 ◇ sK1) ◇ sK2) ≠ (sK2 ◇ (sK0 ◇ sK1)) := superpose eq352 eq397 -- forward demodulation 397,352
  subsumption eq398 eq352


@[equational_result]
theorem Equation3573_implies_Equation4531 (G : Type*) [Magma G] (h : Equation3573 G) : Equation4531 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (X3 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq45 (X0 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq26 -- forward demodulation 26,9
  have eq85 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq45 -- superposition 45,9, 9 into 45, unify on (0).2 in 9 and (0).1 in 45
  have eq98 (X0 X1 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X1)) = (X3 ◇ X1) := superpose eq9 eq85 -- forward demodulation 85,9
  have eq352 (X0 X2 : G) : (X2 ◇ X0) = (X0 ◇ X2) := superpose eq9 eq98 -- superposition 98,9, 9 into 98, unify on (0).2 in 9 and (0).1 in 98
  have eq594 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq352 eq10 -- superposition 10,352, 352 into 10, unify on (0).2 in 352 and (0).2 in 10
  subsumption eq594 rfl


@[equational_result]
theorem Equation3573_implies_Equation4358 (G : Type*) [Magma G] (h : Equation3573 G) : Equation4358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (X3 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq45 (X0 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq26 -- forward demodulation 26,9
  have eq85 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq45 -- superposition 45,9, 9 into 45, unify on (0).2 in 9 and (0).1 in 45
  have eq98 (X0 X1 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X1)) = (X3 ◇ X1) := superpose eq9 eq85 -- forward demodulation 85,9
  have eq352 (X0 X2 : G) : (X2 ◇ X0) = (X0 ◇ X2) := superpose eq9 eq98 -- superposition 98,9, 9 into 98, unify on (0).2 in 9 and (0).1 in 98
  have eq397 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq352 eq10 -- backward demodulation 10,352
  subsumption eq397 rfl


@[equational_result]
theorem Equation3573_implies_Equation43 (G : Type*) [Magma G] (h : Equation3573 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (X3 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq45 (X0 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq26 -- forward demodulation 26,9
  have eq85 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq45 -- superposition 45,9, 9 into 45, unify on (0).2 in 9 and (0).1 in 45
  have eq98 (X0 X1 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X1)) = (X3 ◇ X1) := superpose eq9 eq85 -- forward demodulation 85,9
  have eq352 (X0 X2 : G) : (X2 ◇ X0) = (X0 ◇ X2) := superpose eq9 eq98 -- superposition 98,9, 9 into 98, unify on (0).2 in 9 and (0).1 in 98
  have eq582 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq352 eq10 -- superposition 10,352, 352 into 10, unify on (0).2 in 352 and (0).2 in 10
  subsumption eq582 rfl


@[equational_result]
theorem Equation263_implies_Equation307 (G : Type*) [Magma G] (h : Equation263 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation263_implies_Equation2847 (G : Type*) [Magma G] (h : Equation263 G) : Equation2847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq8


@[equational_result]
theorem Equation263_implies_Equation2644 (G : Type*) [Magma G] (h : Equation263 G) : Equation2644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.1 in 8
  have eq20 : sK0 ≠ sK0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq20 rfl


@[equational_result]
theorem Equation2655_implies_Equation255 (G : Type*) [Magma G] (h : Equation2655 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X3 : G) : (((X3 ◇ X3) ◇ X0) ◇ X3) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq16 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq16 rfl


@[equational_result]
theorem Equation2655_implies_Equation257 (G : Type*) [Magma G] (h : Equation2655 G) : Equation257 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X3 : G) : (((X3 ◇ X3) ◇ X0) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation1264_implies_Equation1256 (G : Type*) [Magma G] (h : Equation1264 G) : Equation1256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq19 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) = X2 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2.1 in 9
  have eq77 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq77 rfl


@[equational_result]
theorem Equation1264_implies_Equation1226 (G : Type*) [Magma G] (h : Equation1264 G) : Equation1226 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) = X2 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2.1 in 9
  have eq68 : sK0 ≠ sK0 := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq68 rfl


@[equational_result]
theorem Equation1264_implies_Equation1248 (G : Type*) [Magma G] (h : Equation1264 G) : Equation1248 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq19 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) = X2 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2.1 in 9
  have eq77 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq77 rfl


@[equational_result]
theorem Equation616_implies_Equation47 (G : Type*) [Magma G] (h : Equation616 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.1 in 8
  have eq11 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq11 rfl


@[equational_result]
theorem Equation731_implies_Equation4307 (G : Type*) [Magma G] (h : Equation731 G) : Equation4307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X3 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq42 (X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X2)) = (X4 ◇ (X4 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1 in 11
  have eq101 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (X0 ◇ sK1)) := superpose eq42 eq10 -- superposition 10,42, 42 into 10, unify on (0).2 in 42 and (0).2 in 10
  subsumption eq101 eq42


@[equational_result]
theorem Equation731_implies_Equation4622 (G : Type*) [Magma G] (h : Equation731 G) : Equation4622 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = ((X0 ◇ X0) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((X0 ◇ X0) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq23 eq12


@[equational_result]
theorem Equation2249_implies_Equation205 (G : Type*) [Magma G] (h : Equation2249 G) : Equation205 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X3 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation909_implies_Equation3862 (G : Type*) [Magma G] (h : Equation909 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq8 -- backward demodulation 8,10
  have eq17 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).1.2 in 11
  have eq22 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).1.2 in 17
  have eq24 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq10 eq22 -- forward demodulation 22,10
  have eq30 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq24 eq9 -- superposition 9,24, 24 into 9, unify on (0).2 in 24 and (0).2 in 9
  subsumption eq30 rfl


@[equational_result]
theorem Equation909_implies_Equation3887 (G : Type*) [Magma G] (h : Equation909 G) : Equation3887 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq13 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq14 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).1.2 in 12
  have eq15 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq14 -- forward demodulation 14,11
  have eq18 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq23 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).1.2 in 18
  have eq25 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq11 eq23 -- forward demodulation 23,11
  have eq43 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.2.2 in 12
  have eq49 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq43 eq10 -- backward demodulation 10,43
  subsumption eq49 eq25


@[equational_result]
theorem Equation909_implies_Equation4307 (G : Type*) [Magma G] (h : Equation909 G) : Equation4307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq13 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq14 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).1.2 in 12
  have eq15 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq14 -- forward demodulation 14,11
  have eq43 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.2.2 in 12
  have eq52 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq43 eq43 -- superposition 43,43, 43 into 43, unify on (0).2 in 43 and (0).1 in 43
  have eq62 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq43 eq10 -- superposition 10,43, 43 into 10, unify on (0).2 in 43 and (0).2 in 10
  subsumption eq62 eq52


@[equational_result]
theorem Equation910_implies_Equation1629 (G : Type*) [Magma G] (h : Equation910 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := superpose eq10 eq8 -- backward demodulation 8,10
  have eq16 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X1 := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).1.2.2.2 in 11
  have eq19 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1.2.2 in 16
  have eq35 : sK0 ≠ sK0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2 in 9
  subsumption eq35 rfl


@[equational_result]
theorem Equation3274_implies_Equation3278 (G : Type*) [Magma G] (h : Equation3274 G) : Equation3278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1))) = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq17 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X0) = (X2 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq22 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))) = (X3 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq32 (X0 X2 : G) : (X0 ◇ X0) = ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq18 eq22 -- forward demodulation 22,18
  have eq33 (X1 X2 X3 : G) : (X1 ◇ X1) = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq32 eq16 -- backward demodulation 16,32
  have eq83 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ (sK0 ◇ sK0))) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2.2 in 10
  subsumption eq83 eq33


@[equational_result]
theorem Equation3274_implies_Equation3258 (G : Type*) [Magma G] (h : Equation3274 G) : Equation3258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1))) = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq17 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X0) = (X2 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq22 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))) = (X3 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq32 (X0 X2 : G) : (X0 ◇ X0) = ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq18 eq22 -- forward demodulation 22,18
  have eq33 (X1 X2 X3 : G) : (X1 ◇ X1) = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq32 eq16 -- backward demodulation 16,32
  have eq83 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2.2 in 10
  subsumption eq83 eq33


@[equational_result]
theorem Equation3274_implies_Equation3288 (G : Type*) [Magma G] (h : Equation3274 G) : Equation3288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1))) = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq17 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X0) = (X2 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq22 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))) = (X3 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq32 (X0 X2 : G) : (X0 ◇ X0) = ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq18 eq22 -- forward demodulation 22,18
  have eq33 (X1 X2 X3 : G) : (X1 ◇ X1) = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq32 eq16 -- backward demodulation 16,32
  have eq83 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ (sK0 ◇ sK0))) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2.2 in 10
  subsumption eq83 eq33


@[equational_result]
theorem Equation58_implies_Equation359 (G : Type*) [Magma G] (h : Equation58 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 : G) : (X2 ◇ X0) = ((X2 ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq14 rfl


@[equational_result]
theorem Equation2389_implies_Equation2327 (G : Type*) [Magma G] (h : Equation2389 G) : Equation2327 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X2 ◇ X2)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq14 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) = X2 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.1.2 in 9
  have eq68 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq68 rfl


@[equational_result]
theorem Equation2389_implies_Equation2355 (G : Type*) [Magma G] (h : Equation2389 G) : Equation2355 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X2 ◇ X2)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq14 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) = X2 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.1.2 in 9
  have eq68 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq68 rfl


@[equational_result]
theorem Equation713_implies_Equation47 (G : Type*) [Magma G] (h : Equation713 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.1 in 8
  have eq13 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2.2 in 10
  have eq16 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.2 in 8
  have eq19 : sK0 ≠ sK0 := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2 in 9
  subsumption eq19 rfl


@[equational_result]
theorem Equation53_implies_Equation1038 (G : Type*) [Magma G] (h : Equation53 G) : Equation1038 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation2385_implies_Equation2406 (G : Type*) [Magma G] (h : Equation2385 G) : Equation2406 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2.2 in 9
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) = X2 := superpose eq12 eq20 -- forward demodulation 20,12
  have eq61 : sK0 ≠ sK0 := superpose eq25 eq10 -- superposition 10,25, 25 into 10, unify on (0).2 in 25 and (0).2 in 10
  subsumption eq61 rfl


@[equational_result]
theorem Equation450_implies_Equation426 (G : Type*) [Magma G] (h : Equation450 G) : Equation426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X3 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2.2 in 9
  have eq55 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))))) = ((X3 ◇ (X4 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))))) ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq59 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ (X4 ◇ (X2 ◇ (X3 ◇ X2))))) = ((X4 ◇ (X5 ◇ (X4 ◇ (X2 ◇ (X3 ◇ X2))))) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq429 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2))))) ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2))))))) = (((X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2))))) ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2))))))) ◇ (((X2 ◇ (X3 ◇ X2)) ◇ (X4 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X2)))) ◇ (X4 ◇ X2))) := superpose eq59 eq55 -- superposition 55,59, 59 into 55, unify on (0).2 in 59 and (0).1.2.2 in 55
  have eq7503 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2))))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2)))))))) = X2 := superpose eq429 eq9 -- superposition 9,429, 429 into 9, unify on (0).2 in 429 and (0).1.2 in 9
  have eq7526 (X0 X1 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X0 ◇ (X3 ◇ X0)) ◇ (X4 ◇ (X0 ◇ (X3 ◇ X0))))) := superpose eq16 eq7503 -- superposition 7503,16, 16 into 7503, unify on (0).2 in 16 and (0).1.2.1.2.2 in 7503
  have eq7574 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7526 eq9 -- superposition 9,7526, 7526 into 9, unify on (0).2 in 7526 and (0).1.2 in 9
  have eq8208 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq7574 eq9 -- superposition 9,7574, 7574 into 9, unify on (0).2 in 7574 and (0).1.2.2 in 9
  have eq8370 : sK0 ≠ sK0 := superpose eq8208 eq10 -- superposition 10,8208, 8208 into 10, unify on (0).2 in 8208 and (0).2 in 10
  subsumption eq8370 rfl


@[equational_result]
theorem Equation450_implies_Equation413 (G : Type*) [Magma G] (h : Equation450 G) : Equation413 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X3 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2.2 in 9
  have eq55 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))))) = ((X3 ◇ (X4 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))))) ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq59 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ (X4 ◇ (X2 ◇ (X3 ◇ X2))))) = ((X4 ◇ (X5 ◇ (X4 ◇ (X2 ◇ (X3 ◇ X2))))) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq429 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2))))) ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2))))))) = (((X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2))))) ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2))))))) ◇ (((X2 ◇ (X3 ◇ X2)) ◇ (X4 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X2)))) ◇ (X4 ◇ X2))) := superpose eq59 eq55 -- superposition 55,59, 59 into 55, unify on (0).2 in 59 and (0).1.2.2 in 55
  have eq7620 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2))))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2)))))))) = X2 := superpose eq429 eq9 -- superposition 9,429, 429 into 9, unify on (0).2 in 429 and (0).1.2 in 9
  have eq7643 (X0 X1 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X0 ◇ (X3 ◇ X0)) ◇ (X4 ◇ (X0 ◇ (X3 ◇ X0))))) := superpose eq16 eq7620 -- superposition 7620,16, 16 into 7620, unify on (0).2 in 16 and (0).1.2.1.2.2 in 7620
  have eq7691 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7643 eq9 -- superposition 9,7643, 7643 into 9, unify on (0).2 in 7643 and (0).1.2 in 9
  have eq7750 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq7691 eq9 -- superposition 9,7691, 7691 into 9, unify on (0).2 in 7691 and (0).1.2.2 in 9
  have eq7912 : sK0 ≠ sK0 := superpose eq7750 eq10 -- superposition 10,7750, 7750 into 10, unify on (0).2 in 7750 and (0).2 in 10
  subsumption eq7912 rfl


@[equational_result]
theorem Equation450_implies_Equation432 (G : Type*) [Magma G] (h : Equation450 G) : Equation432 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X3 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2.2 in 9
  have eq55 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))))) = ((X3 ◇ (X4 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))))) ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq59 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ (X4 ◇ (X2 ◇ (X3 ◇ X2))))) = ((X4 ◇ (X5 ◇ (X4 ◇ (X2 ◇ (X3 ◇ X2))))) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq429 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2))))) ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2))))))) = (((X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2))))) ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2))))))) ◇ (((X2 ◇ (X3 ◇ X2)) ◇ (X4 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X2)))) ◇ (X4 ◇ X2))) := superpose eq59 eq55 -- superposition 55,59, 59 into 55, unify on (0).2 in 59 and (0).1.2.2 in 55
  have eq7654 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2))))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2)))))))) = X2 := superpose eq429 eq9 -- superposition 9,429, 429 into 9, unify on (0).2 in 429 and (0).1.2 in 9
  have eq7677 (X0 X1 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X0 ◇ (X3 ◇ X0)) ◇ (X4 ◇ (X0 ◇ (X3 ◇ X0))))) := superpose eq16 eq7654 -- superposition 7654,16, 16 into 7654, unify on (0).2 in 16 and (0).1.2.1.2.2 in 7654
  have eq7725 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7677 eq9 -- superposition 9,7677, 7677 into 9, unify on (0).2 in 7677 and (0).1.2 in 9
  have eq7784 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq7725 eq9 -- superposition 9,7725, 7725 into 9, unify on (0).2 in 7725 and (0).1.2.2 in 9
  have eq7946 : sK0 ≠ sK0 := superpose eq7784 eq10 -- superposition 10,7784, 7784 into 10, unify on (0).2 in 7784 and (0).2 in 10
  subsumption eq7946 rfl


@[equational_result]
theorem Equation414_implies_Equation3659 (G : Type*) [Magma G] (h : Equation414 G) : Equation3659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation1247_implies_Equation3660 (G : Type*) [Magma G] (h : Equation1247 G) : Equation3660 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X5)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq53 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.2.1 in 12
  have eq160 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq53 eq10 -- superposition 10,53, 53 into 10, unify on (0).2 in 53 and (0).2 in 10
  subsumption eq160 rfl


@[equational_result]
theorem Equation1247_implies_Equation3727 (G : Type*) [Magma G] (h : Equation1247 G) : Equation3727 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X5)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq47 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.2.1 in 12
  have eq175 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq47 eq16 -- superposition 16,47, 47 into 16, unify on (0).2 in 47 and (0).1.2 in 16
  have eq256 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq175 eq10 -- superposition 10,175, 175 into 10, unify on (0).2 in 175 and (0).2 in 10
  subsumption eq256 rfl


@[equational_result]
theorem Equation1887_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1887 G) : Equation1020 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation273_implies_Equation2459 (G : Type*) [Magma G] (h : Equation273 G) : Equation2459 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation1021_implies_Equation47 (G : Type*) [Magma G] (h : Equation1021 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq11 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq11 rfl


@[equational_result]
theorem Equation844_implies_Equation107 (G : Type*) [Magma G] (h : Equation844 G) : Equation107 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation2402_implies_Equation2246 (G : Type*) [Magma G] (h : Equation2402 G) : Equation2246 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq14 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) = X2 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.1 in 9
  have eq68 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq68 rfl


@[equational_result]
theorem Equation2402_implies_Equation2327 (G : Type*) [Magma G] (h : Equation2402 G) : Equation2327 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq14 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) = X2 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.1 in 9
  have eq68 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq68 rfl


@[equational_result]
theorem Equation2402_implies_Equation2355 (G : Type*) [Magma G] (h : Equation2402 G) : Equation2355 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq14 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) = X2 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.1 in 9
  have eq68 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq68 rfl


@[equational_result]
theorem Equation1267_implies_Equation1256 (G : Type*) [Magma G] (h : Equation1267 G) : Equation1256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X1)) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq20 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) = X2 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2 in 9
  have eq77 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq77 rfl


@[equational_result]
theorem Equation1240_implies_Equation104 (G : Type*) [Magma G] (h : Equation1240 G) : Equation104 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation3507_implies_Equation3272 (G : Type*) [Magma G] (h : Equation3507 G) : Equation3272 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X3) ◇ X4)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq16 (X5 X6 X7 : G) : (X6 ◇ X6) = (X7 ◇ (X5 ◇ X5)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq67 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2 in 10
  subsumption eq67 eq16


@[equational_result]
theorem Equation1724_implies_Equation3268 (G : Type*) [Magma G] (h : Equation1724 G) : Equation3268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X3 ◇ X3) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X2) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X0)) = ((X3 ◇ X3) ◇ (X0 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq195 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ (X1 ◇ (X0 ◇ X0))) = (X2 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq201 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq255 (X0 X1 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq11 eq195 -- forward demodulation 195,11
  have eq321 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ (sK0 ◇ sK0))) := superpose eq201 eq10 -- superposition 10,201, 201 into 10, unify on (0).2 in 201 and (0).2.2 in 10
  subsumption eq321 eq255


@[equational_result]
theorem Equation1724_implies_Equation3278 (G : Type*) [Magma G] (h : Equation1724 G) : Equation3278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X3 ◇ X3) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X2) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X0)) = ((X3 ◇ X3) ◇ (X0 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq195 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ (X1 ◇ (X0 ◇ X0))) = (X2 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq201 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq255 (X0 X1 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq11 eq195 -- forward demodulation 195,11
  have eq321 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ (sK0 ◇ sK0))) := superpose eq201 eq10 -- superposition 10,201, 201 into 10, unify on (0).2 in 201 and (0).2.2 in 10
  subsumption eq321 eq255


@[equational_result]
theorem Equation1724_implies_Equation3258 (G : Type*) [Magma G] (h : Equation1724 G) : Equation3258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X3 ◇ X3) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X2) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X0)) = ((X3 ◇ X3) ◇ (X0 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq195 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ (X1 ◇ (X0 ◇ X0))) = (X2 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq201 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq255 (X0 X1 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq11 eq195 -- forward demodulation 195,11
  have eq321 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := superpose eq201 eq10 -- superposition 10,201, 201 into 10, unify on (0).2 in 201 and (0).2.2 in 10
  subsumption eq321 eq255


@[equational_result]
theorem Equation1724_implies_Equation3288 (G : Type*) [Magma G] (h : Equation1724 G) : Equation3288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X3 ◇ X3) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X2) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X0)) = ((X3 ◇ X3) ◇ (X0 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq195 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ (X1 ◇ (X0 ◇ X0))) = (X2 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq201 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq255 (X0 X1 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq11 eq195 -- forward demodulation 195,11
  have eq321 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ (sK0 ◇ sK0))) := superpose eq201 eq10 -- superposition 10,201, 201 into 10, unify on (0).2 in 201 and (0).2.2 in 10
  subsumption eq321 eq255


@[equational_result]
theorem Equation118_implies_Equation255 (G : Type*) [Magma G] (h : Equation118 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq13 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2 in 10
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2 in 9
  subsumption eq18 rfl


@[equational_result]
theorem Equation118_implies_Equation4380 (G : Type*) [Magma G] (h : Equation118 G) : Equation4380 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq13 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2 in 10
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.2.1 in 8
  have eq34 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2 in 9
  subsumption eq34 rfl


@[equational_result]
theorem Equation118_implies_Equation203 (G : Type*) [Magma G] (h : Equation118 G) : Equation203 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq13 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2 in 10
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.2.1 in 8
  have eq19 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq17 eq13 -- backward demodulation 13,17
  have eq20 : sK0 ≠ sK0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2 in 9
  subsumption eq20 rfl


@[equational_result]
theorem Equation118_implies_Equation47 (G : Type*) [Magma G] (h : Equation118 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq13 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2 in 10
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.2.1 in 8
  have eq30 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq17 eq8 -- superposition 8,17, 17 into 8, unify on (0).2 in 17 and (0).1.2 in 8
  have eq51 : sK0 ≠ sK0 := superpose eq30 eq9 -- superposition 9,30, 30 into 9, unify on (0).2 in 30 and (0).2 in 9
  subsumption eq51 rfl


@[equational_result]
theorem Equation111_implies_Equation1229 (G : Type*) [Magma G] (h : Equation111 G) : Equation1229 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq29 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation111_implies_Equation1242 (G : Type*) [Magma G] (h : Equation111 G) : Equation1242 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq29 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation111_implies_Equation1228 (G : Type*) [Magma G] (h : Equation111 G) : Equation1228 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq29 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation270_implies_Equation4080 (G : Type*) [Magma G] (h : Equation270 G) : Equation4080 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (((sK1 ◇ sK0) ◇ sK0) ◇ sK0) ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq11 : sK0 ≠ (sK0 ◇ sK0) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).2 in 11
  subsumption eq15 rfl


@[equational_result]
theorem Equation270_implies_Equation2899 (G : Type*) [Magma G] (h : Equation270 G) : Equation2899 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq9


@[equational_result]
theorem Equation270_implies_Equation2696 (G : Type*) [Magma G] (h : Equation270 G) : Equation2696 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq9


@[equational_result]
theorem Equation4075_implies_Equation4069 (G : Type*) [Magma G] (h : Equation4075 G) : Equation4069 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X0) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X2) ◇ X3) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq25 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq25 rfl


@[equational_result]
theorem Equation2260_implies_Equation151 (G : Type*) [Magma G] (h : Equation2260 G) : Equation151 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq18 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1.2.2 in 11
  have eq48 : sK0 ≠ sK0 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).2 in 9
  subsumption eq48 rfl


@[equational_result]
theorem Equation2260_implies_Equation159 (G : Type*) [Magma G] (h : Equation2260 G) : Equation159 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.2 in 12
  have eq49 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq49 rfl


@[equational_result]
theorem Equation1668_implies_Equation1875 (G : Type*) [Magma G] (h : Equation1668 G) : Equation1875 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X0 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X0 X3 X4 : G) : ((X3 ◇ (X0 ◇ X4)) ◇ (X4 ◇ X3)) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2.1 in 12
  have eq50 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation4080_implies_Equation359 (G : Type*) [Magma G] (h : Equation4080 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1 in 8
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation4154_implies_Equation3253 (G : Type*) [Magma G] (h : Equation4154 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1 in 8
  have eq15 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).2.1 in 8
  have eq18 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq15 -- superposition 15,11, 11 into 15, unify on (0).2 in 11 and (0).2 in 15
  have eq22 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq18 -- forward demodulation 18,11
  have eq26 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq22 eq9 -- superposition 9,22, 22 into 9, unify on (0).2 in 22 and (0).2 in 9
  subsumption eq26 rfl


@[equational_result]
theorem Equation3355_implies_Equation4065 (G : Type*) [Magma G] (h : Equation3355 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.2 in 8
  have eq12 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2 in 12
  have eq18 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq11 eq16 -- forward demodulation 16,11
  subsumption eq18 eq8


@[equational_result]
theorem Equation3078_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3078 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq9 -- backward demodulation 9,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3078_implies_Equation307 (G : Type*) [Magma G] (h : Equation3078 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq13 rfl


@[equational_result]
theorem Equation2862_implies_Equation255 (G : Type*) [Magma G] (h : Equation2862 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.2 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation2850_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2850 G) : Equation2035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1 in 8
  have eq12 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).1 in 10
  have eq13 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ X1) ◇ X1) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.1 in 8
  have eq20 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X2) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1 in 13
  have eq24 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).1.1 in 12
  have eq63 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ X0) ◇ (sK0 ◇ sK0)) := superpose eq20 eq9 -- superposition 9,20, 20 into 9, unify on (0).2 in 20 and (0).2.1 in 9
  subsumption eq63 eq24


@[equational_result]
theorem Equation2850_implies_Equation2060 (G : Type*) [Magma G] (h : Equation2850 G) : Equation2060 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq13 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq26 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq14 eq13 -- superposition 13,14, 14 into 13, unify on (0).2 in 14 and (0).1.1 in 13
  have eq64 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ X0) ◇ (sK0 ◇ sK0)) := superpose eq24 eq10 -- superposition 10,24, 24 into 10, unify on (0).2 in 24 and (0).2.1 in 10
  subsumption eq64 eq26


@[equational_result]
theorem Equation2850_implies_Equation4656 (G : Type*) [Magma G] (h : Equation2850 G) : Equation4656 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq64 (X0 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK0 ◇ X0) ◇ X0) := superpose eq24 eq10 -- superposition 10,24, 24 into 10, unify on (0).2 in 24 and (0).2 in 10
  subsumption eq64 eq24


@[equational_result]
theorem Equation2649_implies_Equation255 (G : Type*) [Magma G] (h : Equation2649 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation2493_implies_Equation255 (G : Type*) [Magma G] (h : Equation2493 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation2447_implies_Equation1629 (G : Type*) [Magma G] (h : Equation2447 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation2101_implies_Equation817 (G : Type*) [Magma G] (h : Equation2101 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation2098_implies_Equation47 (G : Type*) [Magma G] (h : Equation2098 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq13 rfl


@[equational_result]
theorem Equation1645_implies_Equation2441 (G : Type*) [Magma G] (h : Equation1645 G) : Equation2441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq13 rfl


@[equational_result]
theorem Equation1526_implies_Equation2644 (G : Type*) [Magma G] (h : Equation1526 G) : Equation2644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation1491_implies_Equation4065 (G : Type*) [Magma G] (h : Equation1491 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2 in 10
  have eq32 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2 in 11
  have eq37 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq32 eq9 -- backward demodulation 9,32
  subsumption eq37 eq32


@[equational_result]
theorem Equation1491_implies_Equation3862 (G : Type*) [Magma G] (h : Equation1491 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2 in 10
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2 in 8
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1 in 8
  have eq32 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2 in 11
  have eq60 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq32 eq15 -- superposition 15,32, 32 into 15, unify on (0).2 in 32 and (0).1 in 15
  have eq65 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq14 eq60 -- forward demodulation 60,14
  have eq66 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq10 eq65 -- forward demodulation 65,10
  have eq137 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq66 eq9 -- superposition 9,66, 66 into 9, unify on (0).2 in 66 and (0).2 in 9
  subsumption eq137 rfl


@[equational_result]
theorem Equation1491_implies_Equation817 (G : Type*) [Magma G] (h : Equation1491 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2 in 10
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = ((X0 ◇ X1) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.2 in 10
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2 in 8
  have eq32 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2 in 11
  have eq63 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).1.2 in 10
  have eq68 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq10 eq63 -- forward demodulation 63,10
  have eq70 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq68 eq9 -- backward demodulation 9,68
  have eq91 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq32 eq12 -- superposition 12,32, 32 into 12, unify on (0).2 in 32 and (0).1.2.2.1 in 12
  have eq105 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq12 eq91 -- forward demodulation 91,12
  have eq106 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq14 eq105 -- forward demodulation 105,14
  have eq107 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq106 -- forward demodulation 106,10
  have eq122 : sK0 ≠ sK0 := superpose eq107 eq70 -- superposition 70,107, 107 into 70, unify on (0).2 in 107 and (0).2 in 70
  subsumption eq122 rfl


@[equational_result]
theorem Equation1491_implies_Equation614 (G : Type*) [Magma G] (h : Equation1491 G) : Equation614 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq10 eq9 -- backward demodulation 9,10
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2 in 10
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = ((X0 ◇ X1) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.2 in 10
  have eq15 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2 in 8
  have eq33 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2 in 12
  have eq91 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq33 eq13 -- superposition 13,33, 33 into 13, unify on (0).2 in 33 and (0).1.2.2.1 in 13
  have eq105 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq13 eq91 -- forward demodulation 91,13
  have eq106 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq15 eq105 -- forward demodulation 105,15
  have eq107 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq106 -- forward demodulation 106,10
  have eq117 : sK0 ≠ sK0 := superpose eq107 eq11 -- superposition 11,107, 107 into 11, unify on (0).2 in 107 and (0).2 in 11
  subsumption eq117 rfl


@[equational_result]
theorem Equation1491_implies_Equation359 (G : Type*) [Magma G] (h : Equation1491 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2 in 10
  have eq32 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2 in 11
  have eq65 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq32 eq9 -- superposition 9,32, 32 into 9, unify on (0).2 in 32 and (0).2 in 9
  subsumption eq65 rfl


@[equational_result]
theorem Equation1491_implies_Equation47 (G : Type*) [Magma G] (h : Equation1491 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2 in 10
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = ((X0 ◇ X1) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.2 in 10
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2 in 8
  have eq32 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2 in 11
  have eq80 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq32 eq12 -- superposition 12,32, 32 into 12, unify on (0).2 in 32 and (0).1.2.2.1 in 12
  have eq93 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq12 eq80 -- forward demodulation 80,12
  have eq94 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq14 eq93 -- forward demodulation 93,14
  have eq95 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq94 -- forward demodulation 94,10
  have eq98 : sK0 ≠ sK0 := superpose eq95 eq9 -- superposition 9,95, 95 into 9, unify on (0).2 in 95 and (0).2 in 9
  subsumption eq98 rfl


@[equational_result]
theorem Equation1489_implies_Equation255 (G : Type*) [Magma G] (h : Equation1489 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq15 rfl


@[equational_result]
theorem Equation1444_implies_Equation4065 (G : Type*) [Magma G] (h : Equation1444 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq15 rfl


@[equational_result]
theorem Equation1323_implies_Equation2644 (G : Type*) [Magma G] (h : Equation1323 G) : Equation2644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq13 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2 in 8
  have eq20 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq25 : sK0 ≠ sK0 := superpose eq20 eq9 -- superposition 9,20, 20 into 9, unify on (0).2 in 20 and (0).2 in 9
  subsumption eq25 rfl


@[equational_result]
theorem Equation1082_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1082 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation822_implies_Equation47 (G : Type*) [Magma G] (h : Equation822 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq11 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq11 rfl


@[equational_result]
theorem Equation818_implies_Equation99 (G : Type*) [Magma G] (h : Equation818 G) : Equation99 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq11 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq11 rfl


@[equational_result]
theorem Equation615_implies_Equation47 (G : Type*) [Magma G] (h : Equation615 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq11 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq11 rfl


@[equational_result]
theorem Equation219_implies_Equation817 (G : Type*) [Magma G] (h : Equation219 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation219_implies_Equation873 (G : Type*) [Magma G] (h : Equation219 G) : Equation873 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq13 rfl


@[equational_result]
theorem Equation880_implies_Equation4647 (G : Type*) [Magma G] (h : Equation880 G) : Equation4647 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK2 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq19 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2 in 12
  have eq67 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.1.1 in 11
  have eq90 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ sK1) := superpose eq67 eq10 -- superposition 10,67, 67 into 10, unify on (0).2 in 67 and (0).2 in 10
  subsumption eq90 eq67


@[equational_result]
theorem Equation117_implies_Equation2035 (G : Type*) [Magma G] (h : Equation117 G) : Equation2035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq13 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq13 rfl


@[equational_result]
theorem Equation117_implies_Equation2100 (G : Type*) [Magma G] (h : Equation117 G) : Equation2100 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq14 rfl


@[equational_result]
theorem Equation115_implies_Equation2644 (G : Type*) [Magma G] (h : Equation115 G) : Equation2644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation115_implies_Equation2734 (G : Type*) [Magma G] (h : Equation115 G) : Equation2734 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq13 rfl


