import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation2960_implies_Equation706 (G : Type*) [Magma G] (h : Equation2960 G) : Equation706 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq21 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq28 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X3 := superpose eq21 eq13 -- backward demodulation 13,21
  have eq29 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq21 eq9 -- backward demodulation 9,21
  have eq30 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq28 eq10 -- backward demodulation 10,28
  have eq36 : sK0 ≠ (sK1 ◇ sK0) := superpose eq29 eq30 -- backward demodulation 30,29
  subsumption eq36 eq29


@[equational_result]
theorem Equation2960_implies_Equation4554 (G : Type*) [Magma G] (h : Equation2960 G) : Equation4554 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq21 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq28 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X3 := superpose eq21 eq13 -- backward demodulation 13,21
  have eq29 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq21 eq9 -- backward demodulation 9,21
  have eq30 : sK2 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq28 eq10 -- backward demodulation 10,28
  have eq36 : sK2 ≠ (sK0 ◇ sK2) := superpose eq29 eq30 -- backward demodulation 30,29
  subsumption eq36 eq29


@[equational_result]
theorem Equation2960_implies_Equation2525 (G : Type*) [Magma G] (h : Equation2960 G) : Equation2525 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK2) ◇ sK3)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq21 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq28 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X3 := superpose eq21 eq13 -- backward demodulation 13,21
  have eq30 : sK0 ≠ ((sK1 ◇ sK3) ◇ sK0) := superpose eq28 eq10 -- backward demodulation 10,28
  subsumption eq30 eq28


@[equational_result]
theorem Equation3163_implies_Equation3541 (G : Type*) [Magma G] (h : Equation3163 G) : Equation3541 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK3) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq16 rfl


@[equational_result]
theorem Equation3163_implies_Equation2633 (G : Type*) [Magma G] (h : Equation3163 G) : Equation2633 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK3) ◇ sK3)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ ((sK1 ◇ sK3) ◇ sK0) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq16 eq15


@[equational_result]
theorem Equation3163_implies_Equation3667 (G : Type*) [Magma G] (h : Equation3163 G) : Equation3667 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 (X2 X3 : G) : (X2 ◇ X3) = X3 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.1 in 15
  have eq21 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq16 eq10 -- backward demodulation 10,16
  have eq22 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq16 eq21 -- forward demodulation 21,16
  have eq23 : sK0 ≠ (sK0 ◇ sK0) := superpose eq16 eq22 -- forward demodulation 22,16
  subsumption eq23 eq16


@[equational_result]
theorem Equation3163_implies_Equation3634 (G : Type*) [Magma G] (h : Equation3163 G) : Equation3634 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK3 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK1) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq17 (X2 X3 : G) : (X2 ◇ X3) = X3 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.1 in 15
  have eq21 : sK1 ≠ (sK2 ◇ sK1) := superpose eq17 eq16 -- backward demodulation 16,17
  subsumption eq21 eq17


@[equational_result]
theorem Equation2579_implies_Equation2720 (G : Type*) [Magma G] (h : Equation2579 G) : Equation2720 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK2 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X4) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq28 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq28 rfl


@[equational_result]
theorem Equation2728_implies_Equation3556 (G : Type*) [Magma G] (h : Equation2728 G) : Equation3556 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X1 X4 X5 : G) : (((X4 ◇ X5) ◇ X1) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ (X3 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X0) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq15 (X1 X5 : G) : (X1 ◇ X5) = X5 := superpose eq14 eq12 -- backward demodulation 12,14
  have eq16 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq20 : sK1 ≠ (sK0 ◇ sK1) := superpose eq15 eq16 -- forward demodulation 16,15
  subsumption eq20 eq15


@[equational_result]
theorem Equation2728_implies_Equation2960 (G : Type*) [Magma G] (h : Equation2728 G) : Equation2960 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X1 X4 X5 : G) : ((X1 ◇ (X4 ◇ X5)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X1 X4 X5 : G) : (((X4 ◇ X5) ◇ X1) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ (X3 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (sK1 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq15 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X0) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq16 (X1 X5 : G) : (X1 ◇ X5) = X5 := superpose eq15 eq12 -- backward demodulation 12,15
  have eq20 : sK0 ≠ sK0 := superpose eq16 eq14 -- superposition 14,16, 16 into 14, unify on (0).2 in 16 and (0).2 in 14
  subsumption eq20 rfl


@[equational_result]
theorem Equation3130_implies_Equation4542 (G : Type*) [Magma G] (h : Equation3130 G) : Equation4542 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq13 eq12 -- backward demodulation 12,13
  have eq17 : sK2 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK2 ≠ (sK0 ◇ sK2) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation3130_implies_Equation2633 (G : Type*) [Magma G] (h : Equation3130 G) : Equation2633 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK3) ◇ sK3)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq13 eq12 -- backward demodulation 12,13
  have eq17 : sK0 ≠ ((sK1 ◇ sK3) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation3130_implies_Equation2499 (G : Type*) [Magma G] (h : Equation3130 G) : Equation2499 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ ((sK1 ◇ sK2) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq13 eq12 -- backward demodulation 12,13
  have eq18 : sK0 ≠ (sK2 ◇ sK0) := superpose eq15 eq14 -- backward demodulation 14,15
  subsumption eq18 eq15


@[equational_result]
theorem Equation3130_implies_Equation3687 (G : Type*) [Magma G] (h : Equation3130 G) : Equation3687 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq13 eq12 -- backward demodulation 12,13
  have eq15 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq14 eq15 -- forward demodulation 15,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation2628_implies_Equation2521 (G : Type*) [Magma G] (h : Equation2628 G) : Equation2521 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK2) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 : sK0 ≠ ((sK1 ◇ sK2) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation294_implies_Equation2509 (G : Type*) [Magma G] (h : Equation294 G) : Equation2509 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK1) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ ((sK1 ◇ sK2) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq14


@[equational_result]
theorem Equation3029_implies_Equation294 (G : Type*) [Magma G] (h : Equation3029 G) : Equation294 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : (((X4 ◇ X3) ◇ X4) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2525_implies_Equation3029 (G : Type*) [Magma G] (h : Equation2525 G) : Equation3029 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK3)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : ((X4 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 : sK0 ≠ (sK1 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 (X2 X3 : G) : (X2 ◇ X3) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq19 : sK0 ≠ sK0 := superpose eq17 eq16 -- superposition 16,17, 17 into 16, unify on (0).2 in 17 and (0).2 in 16
  subsumption eq19 rfl


@[equational_result]
theorem Equation2509_implies_Equation2923 (G : Type*) [Magma G] (h : Equation2509 G) : Equation2923 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK2)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq26 : sK0 ≠ (sK1 ◇ sK0) := superpose eq17 eq10 -- backward demodulation 10,17
  subsumption eq26 eq17


@[equational_result]
theorem Equation2633_implies_Equation4490 (G : Type*) [Magma G] (h : Equation2633 G) : Equation4490 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X3 X4 X5 : G) : (((X3 ◇ X4) ◇ X4) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq26 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq38 : sK1 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq26 eq10 -- backward demodulation 10,26
  have eq39 : sK1 ≠ (sK0 ◇ sK1) := superpose eq26 eq38 -- forward demodulation 38,26
  subsumption eq39 eq26


@[equational_result]
theorem Equation2633_implies_Equation537 (G : Type*) [Magma G] (h : Equation2633 G) : Equation537 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq13 (X3 X4 X5 : G) : (((X3 ◇ X4) ◇ X4) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq26 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq38 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := superpose eq26 eq10 -- backward demodulation 10,26
  have eq39 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq26 eq38 -- forward demodulation 38,26
  have eq40 : sK0 ≠ (sK1 ◇ sK0) := superpose eq26 eq39 -- forward demodulation 39,26
  subsumption eq40 eq26


@[equational_result]
theorem Equation2633_implies_Equation2579 (G : Type*) [Magma G] (h : Equation2633 G) : Equation2579 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK0) ◇ sK3)) ◇ sK0) := mod_symm nh
  have eq13 (X3 X4 X5 : G) : (((X3 ◇ X4) ◇ X4) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq26 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq38 : sK0 ≠ ((sK1 ◇ sK3) ◇ sK0) := superpose eq26 eq10 -- backward demodulation 10,26
  subsumption eq38 eq26


@[equational_result]
theorem Equation3015_implies_Equation1713 (G : Type*) [Magma G] (h : Equation3015 G) : Equation1713 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK3) ◇ sK0)) := mod_symm nh
  have eq13 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq13


@[equational_result]
theorem Equation3015_implies_Equation3566 (G : Type*) [Magma G] (h : Equation3015 G) : Equation3566 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq13 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 : sK1 ≠ (sK0 ◇ sK1) := superpose eq13 eq17 -- forward demodulation 17,13
  subsumption eq18 eq13


@[equational_result]
theorem Equation3015_implies_Equation318 (G : Type*) [Magma G] (h : Equation3015 G) : Equation318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq13 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 : sK0 ≠ (sK1 ◇ sK0) := superpose eq13 eq17 -- forward demodulation 17,13
  subsumption eq18 eq13


@[equational_result]
theorem Equation3015_implies_Equation2720 (G : Type*) [Magma G] (h : Equation3015 G) : Equation2720 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK2 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 : sK0 ≠ ((sK2 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq13


@[equational_result]
theorem Equation3015_implies_Equation3503 (G : Type*) [Magma G] (h : Equation3015 G) : Equation3503 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ sK0)) := mod_symm nh
  have eq13 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq17 -- forward demodulation 17,13
  subsumption eq18 eq13


@[equational_result]
theorem Equation2521_implies_Equation709 (G : Type*) [Magma G] (h : Equation2521 G) : Equation709 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq70 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq82 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq70 eq9 -- backward demodulation 9,70
  have eq83 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq70 eq12 -- backward demodulation 12,70
  have eq87 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq82 eq10 -- backward demodulation 10,82
  have eq90 : sK0 ≠ (sK1 ◇ sK0) := superpose eq83 eq87 -- backward demodulation 87,83
  subsumption eq90 eq83


@[equational_result]
theorem Equation2521_implies_Equation875 (G : Type*) [Magma G] (h : Equation2521 G) : Equation875 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq70 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq82 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := superpose eq57 eq10 -- backward demodulation 10,57
  have eq84 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq70 eq12 -- backward demodulation 12,70
  have eq90 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq84 eq82 -- forward demodulation 82,84
  have eq91 : sK0 ≠ (sK1 ◇ sK0) := superpose eq84 eq90 -- forward demodulation 90,84
  subsumption eq91 eq84


@[equational_result]
theorem Equation2521_implies_Equation3661 (G : Type*) [Magma G] (h : Equation2521 G) : Equation3661 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq70 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq82 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq57 eq10 -- backward demodulation 10,57
  have eq84 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq70 eq12 -- backward demodulation 12,70
  have eq90 : sK0 ≠ (sK0 ◇ sK0) := superpose eq84 eq82 -- forward demodulation 82,84
  subsumption eq90 eq57


@[equational_result]
theorem Equation2521_implies_Equation3529 (G : Type*) [Magma G] (h : Equation2521 G) : Equation3529 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq70 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq82 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq70 eq9 -- backward demodulation 9,70
  have eq87 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq82 eq10 -- backward demodulation 10,82
  subsumption eq87 rfl


@[equational_result]
theorem Equation2521_implies_Equation4399 (G : Type*) [Magma G] (h : Equation2521 G) : Equation4399 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq75 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq88 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq75 eq12 -- backward demodulation 12,75
  have eq95 : sK1 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq75 eq10 -- backward demodulation 10,75
  have eq99 : sK1 ≠ (sK0 ◇ sK1) := superpose eq88 eq95 -- forward demodulation 95,88
  subsumption eq99 eq88


@[equational_result]
theorem Equation2521_implies_Equation2808 (G : Type*) [Magma G] (h : Equation2521 G) : Equation2808 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK2 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq70 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq82 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq70 eq9 -- backward demodulation 9,70
  have eq87 : sK0 ≠ ((sK2 ◇ sK1) ◇ sK0) := superpose eq82 eq10 -- backward demodulation 10,82
  subsumption eq87 eq82


@[equational_result]
theorem Equation2521_implies_Equation2964 (G : Type*) [Magma G] (h : Equation2521 G) : Equation2964 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq75 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq87 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq75 eq9 -- backward demodulation 9,75
  have eq88 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq75 eq12 -- backward demodulation 12,75
  have eq95 : sK0 ≠ (sK2 ◇ sK0) := superpose eq87 eq10 -- backward demodulation 10,87
  have eq99 : sK0 ≠ sK0 := superpose eq88 eq95 -- superposition 95,88, 88 into 95, unify on (0).2 in 88 and (0).2 in 95
  subsumption eq99 rfl


@[equational_result]
theorem Equation2521_implies_Equation315 (G : Type*) [Magma G] (h : Equation2521 G) : Equation315 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq70 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq82 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq57 eq10 -- backward demodulation 10,57
  have eq84 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq70 eq12 -- backward demodulation 12,70
  have eq90 : sK0 ≠ (sK1 ◇ sK0) := superpose eq84 eq82 -- forward demodulation 82,84
  subsumption eq90 eq84


@[equational_result]
theorem Equation2521_implies_Equation3725 (G : Type*) [Magma G] (h : Equation2521 G) : Equation3725 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq47 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  have eq82 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq97 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq82 eq16 -- backward demodulation 16,82
  have eq113 : sK1 ≠ (sK0 ◇ sK1) := superpose eq82 eq47 -- backward demodulation 47,82
  have eq116 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq97 eq12 -- backward demodulation 12,97
  subsumption eq113 eq116


@[equational_result]
theorem Equation2521_implies_Equation3680 (G : Type*) [Magma G] (h : Equation2521 G) : Equation3680 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq70 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq82 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK0)) := superpose eq57 eq10 -- backward demodulation 10,57
  have eq84 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq70 eq12 -- backward demodulation 12,70
  have eq90 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq84 eq82 -- forward demodulation 82,84
  subsumption eq90 eq84


@[equational_result]
theorem Equation2521_implies_Equation4508 (G : Type*) [Magma G] (h : Equation2521 G) : Equation4508 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq70 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq82 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK2) := superpose eq57 eq10 -- backward demodulation 10,57
  have eq84 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq70 eq12 -- backward demodulation 12,70
  have eq90 : sK2 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq84 eq82 -- forward demodulation 82,84
  have eq91 : sK2 ≠ (sK0 ◇ sK2) := superpose eq84 eq90 -- forward demodulation 90,84
  subsumption eq91 eq84


@[equational_result]
theorem Equation2521_implies_Equation2998 (G : Type*) [Magma G] (h : Equation2521 G) : Equation2998 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq70 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq82 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq70 eq9 -- backward demodulation 9,70
  have eq83 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq70 eq12 -- backward demodulation 12,70
  have eq87 : sK0 ≠ (sK2 ◇ sK0) := superpose eq82 eq10 -- backward demodulation 10,82
  have eq90 : sK0 ≠ sK0 := superpose eq83 eq87 -- superposition 87,83, 83 into 87, unify on (0).2 in 83 and (0).2 in 87
  subsumption eq90 rfl


@[equational_result]
theorem Equation2521_implies_Equation4476 (G : Type*) [Magma G] (h : Equation2521 G) : Equation4476 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq70 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq82 : ((sK0 ◇ sK2) ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq57 eq10 -- backward demodulation 10,57
  have eq84 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq70 eq12 -- backward demodulation 12,70
  have eq90 : sK1 ≠ ((sK0 ◇ sK2) ◇ sK1) := superpose eq84 eq82 -- forward demodulation 82,84
  subsumption eq90 eq84


@[equational_result]
theorem Equation2521_implies_Equation3790 (G : Type*) [Magma G] (h : Equation2521 G) : Equation3790 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq70 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq82 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK0) ◇ sK1) := superpose eq57 eq10 -- backward demodulation 10,57
  have eq84 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq70 eq12 -- backward demodulation 12,70
  have eq90 : sK1 ≠ (sK0 ◇ sK1) := superpose eq84 eq82 -- forward demodulation 82,84
  subsumption eq90 eq84


@[equational_result]
theorem Equation2521_implies_Equation2868 (G : Type*) [Magma G] (h : Equation2521 G) : Equation2868 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq70 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq82 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq70 eq9 -- backward demodulation 9,70
  have eq83 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq70 eq12 -- backward demodulation 12,70
  have eq87 : sK0 ≠ (sK2 ◇ sK0) := superpose eq82 eq10 -- backward demodulation 10,82
  have eq90 : sK0 ≠ sK0 := superpose eq83 eq87 -- superposition 87,83, 83 into 87, unify on (0).2 in 83 and (0).2 in 87
  subsumption eq90 rfl


@[equational_result]
theorem Equation2521_implies_Equation3718 (G : Type*) [Magma G] (h : Equation2521 G) : Equation3718 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq70 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq82 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK1)) := superpose eq57 eq10 -- backward demodulation 10,57
  have eq84 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq70 eq12 -- backward demodulation 12,70
  have eq90 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq84 eq82 -- forward demodulation 82,84
  subsumption eq90 rfl


@[equational_result]
theorem Equation2521_implies_Equation3163 (G : Type*) [Magma G] (h : Equation2521 G) : Equation3163 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK2) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq75 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq82 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK1) ◇ sK0) := superpose eq57 eq10 -- backward demodulation 10,57
  have eq89 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq75 eq12 -- backward demodulation 12,75
  subsumption eq82 eq89


@[equational_result]
theorem Equation2521_implies_Equation4424 (G : Type*) [Magma G] (h : Equation2521 G) : Equation4424 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq70 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq82 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ sK1) := superpose eq57 eq10 -- backward demodulation 10,57
  have eq84 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq70 eq12 -- backward demodulation 12,70
  have eq90 : sK1 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq84 eq82 -- forward demodulation 82,84
  have eq91 : sK1 ≠ (sK0 ◇ sK1) := superpose eq84 eq90 -- forward demodulation 90,84
  subsumption eq91 eq84


@[equational_result]
theorem Equation2521_implies_Equation3740 (G : Type*) [Magma G] (h : Equation2521 G) : Equation3740 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq70 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq83 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq70 eq12 -- backward demodulation 12,70
  have eq89 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ sK1)) := superpose eq83 eq10 -- backward demodulation 10,83
  have eq90 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK1) := superpose eq83 eq89 -- forward demodulation 89,83
  have eq91 : sK1 ≠ (sK0 ◇ sK1) := superpose eq83 eq90 -- forward demodulation 90,83
  subsumption eq91 eq83


@[equational_result]
theorem Equation2521_implies_Equation2949 (G : Type*) [Magma G] (h : Equation2521 G) : Equation2949 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq19 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK1) ◇ sK0) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq20 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq22 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq20 -- forward demodulation 20,16
  have eq23 : sK0 ≠ (sK1 ◇ sK0) := superpose eq22 eq19 -- backward demodulation 19,22
  have eq25 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.1 in 12
  have eq32 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq25 eq14 -- backward demodulation 14,25
  have eq34 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq25 eq16 -- backward demodulation 16,25
  have eq38 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq34 eq32 -- backward demodulation 32,34
  have eq44 : sK0 ≠ sK0 := superpose eq38 eq23 -- superposition 23,38, 38 into 23, unify on (0).2 in 38 and (0).2 in 23
  subsumption eq44 rfl


@[equational_result]
theorem Equation2521_implies_Equation4402 (G : Type*) [Magma G] (h : Equation2521 G) : Equation4402 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq75 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq87 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq75 eq9 -- backward demodulation 9,75
  have eq88 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq75 eq12 -- backward demodulation 12,75
  have eq95 : sK1 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq87 eq10 -- backward demodulation 10,87
  have eq99 : sK1 ≠ (sK0 ◇ sK1) := superpose eq88 eq95 -- backward demodulation 95,88
  subsumption eq99 eq88


@[equational_result]
theorem Equation2521_implies_Equation4480 (G : Type*) [Magma G] (h : Equation2521 G) : Equation4480 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq70 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq82 : ((sK1 ◇ sK0) ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq57 eq10 -- backward demodulation 10,57
  have eq84 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq70 eq12 -- backward demodulation 12,70
  have eq90 : sK1 ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq84 eq82 -- forward demodulation 82,84
  subsumption eq90 eq84


@[equational_result]
theorem Equation2521_implies_Equation3690 (G : Type*) [Magma G] (h : Equation2521 G) : Equation3690 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq70 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq82 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK0)) := superpose eq57 eq10 -- backward demodulation 10,57
  have eq84 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq70 eq12 -- backward demodulation 12,70
  have eq90 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq84 eq82 -- forward demodulation 82,84
  subsumption eq90 eq84


@[equational_result]
theorem Equation2521_implies_Equation2420 (G : Type*) [Magma G] (h : Equation2521 G) : Equation2420 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq70 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq83 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq70 eq12 -- backward demodulation 12,70
  have eq89 : sK0 ≠ ((sK2 ◇ (sK3 ◇ sK1)) ◇ sK0) := superpose eq83 eq10 -- backward demodulation 10,83
  subsumption eq89 eq83


@[equational_result]
theorem Equation2521_implies_Equation3515 (G : Type*) [Magma G] (h : Equation2521 G) : Equation3515 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq75 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq87 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq75 eq9 -- backward demodulation 9,75
  have eq95 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq87 eq10 -- backward demodulation 10,87
  subsumption eq95 rfl


@[equational_result]
theorem Equation2521_implies_Equation1887 (G : Type*) [Magma G] (h : Equation2521 G) : Equation1887 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq70 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq82 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := superpose eq57 eq10 -- backward demodulation 10,57
  have eq84 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq70 eq12 -- backward demodulation 12,70
  have eq90 : sK0 ≠ (sK0 ◇ sK0) := superpose eq84 eq82 -- forward demodulation 82,84
  subsumption eq90 eq57


@[equational_result]
theorem Equation2905_implies_Equation4486 (G : Type*) [Magma G] (h : Equation2905 G) : Equation4486 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK1 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK1 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK1 ≠ (sK0 ◇ sK1) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation2905_implies_Equation3491 (G : Type*) [Magma G] (h : Equation2905 G) : Equation3491 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation2905_implies_Equation2994 (G : Type*) [Magma G] (h : Equation2905 G) : Equation2994 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ (sK1 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation2905_implies_Equation5 (G : Type*) [Magma G] (h : Equation2905 G) : Equation5 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2905_implies_Equation4569 (G : Type*) [Magma G] (h : Equation2905 G) : Equation4569 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK2 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK2 ≠ (sK0 ◇ sK2) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation2905_implies_Equation3487 (G : Type*) [Magma G] (h : Equation2905 G) : Equation3487 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation2905_implies_Equation3587 (G : Type*) [Magma G] (h : Equation2905 G) : Equation3587 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK1 ≠ (sK0 ◇ sK1) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation2905_implies_Equation2609 (G : Type*) [Magma G] (h : Equation2905 G) : Equation2609 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK2) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK1 ◇ sK2) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation2905_implies_Equation3583 (G : Type*) [Magma G] (h : Equation2905 G) : Equation3583 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK1 ≠ (sK0 ◇ sK1) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation2905_implies_Equation4537 (G : Type*) [Magma G] (h : Equation2905 G) : Equation4537 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK2 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK2 ≠ (sK0 ◇ sK2) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation2905_implies_Equation2536 (G : Type*) [Magma G] (h : Equation2905 G) : Equation2536 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK1 ◇ sK2) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation2905_implies_Equation3617 (G : Type*) [Magma G] (h : Equation2905 G) : Equation3617 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK2 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK1 ≠ (sK0 ◇ sK1) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation2905_implies_Equation3477 (G : Type*) [Magma G] (h : Equation2905 G) : Equation3477 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK0 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation2905_implies_Equation3591 (G : Type*) [Magma G] (h : Equation2905 G) : Equation3591 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK0 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK1 ≠ (sK0 ◇ sK1) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation2905_implies_Equation3015 (G : Type*) [Magma G] (h : Equation2905 G) : Equation3015 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ (sK2 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation2905_implies_Equation2728 (G : Type*) [Magma G] (h : Equation2905 G) : Equation2728 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK2 ◇ sK3)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK2 ◇ sK3) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation2905_implies_Equation2592 (G : Type*) [Magma G] (h : Equation2905 G) : Equation2592 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK1) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK1 ◇ sK2) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation2905_implies_Equation3214 (G : Type*) [Magma G] (h : Equation2905 G) : Equation3214 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK2) ◇ sK2) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ (sK1 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation2905_implies_Equation3600 (G : Type*) [Magma G] (h : Equation2905 G) : Equation3600 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK1 ≠ (sK0 ◇ sK1) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation2905_implies_Equation4550 (G : Type*) [Magma G] (h : Equation2905 G) : Equation4550 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK2 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK2 ≠ (sK0 ◇ sK2) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation2905_implies_Equation3484 (G : Type*) [Magma G] (h : Equation2905 G) : Equation3484 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation2720_implies_Equation885 (G : Type*) [Magma G] (h : Equation2720 G) : Equation885 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq26 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X2))) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X2)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1 in 12
  have eq32 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X1) = X1 := superpose eq26 eq11 -- backward demodulation 11,26
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq57 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) := superpose eq32 eq12 -- superposition 12,32, 32 into 12, unify on (0).2 in 32 and (0).1.1 in 12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq365 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) := superpose eq57 eq10 -- superposition 10,57, 57 into 10, unify on (0).2 in 57 and (0).2 in 10
  have eq892 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq956 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq892 -- forward demodulation 892,12
  have eq1015 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq956 eq956 -- superposition 956,956, 956 into 956, unify on (0).2 in 956 and (0).2.1 in 956
  have eq1095 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1015 eq9 -- backward demodulation 9,1015
  have eq1139 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1095 eq12 -- backward demodulation 12,1095
  have eq1196 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq1139 eq365 -- backward demodulation 365,1139
  have eq1197 : sK0 ≠ (sK1 ◇ sK0) := superpose eq1139 eq1196 -- forward demodulation 1196,1139
  subsumption eq1197 eq1139


@[equational_result]
theorem Equation2720_implies_Equation4448 (G : Type*) [Magma G] (h : Equation2720 G) : Equation4448 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1321 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq1217 eq10 -- backward demodulation 10,1217
  have eq1324 : sK0 ≠ (sK0 ◇ sK0) := superpose eq1260 eq1321 -- forward demodulation 1321,1260
  subsumption eq1324 eq1260


@[equational_result]
theorem Equation2720_implies_Equation3201 (G : Type*) [Magma G] (h : Equation2720 G) : Equation3201 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK2) ◇ sK1) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : sK0 ≠ (sK2 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq21 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.1.2 in 15
  have eq26 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.1 in 12
  have eq897 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq26 eq99 -- superposition 99,26, 26 into 99, unify on (0).2 in 26 and (0).1.2.1 in 99
  have eq961 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq897 -- forward demodulation 897,12
  have eq1020 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq961 eq961 -- superposition 961,961, 961 into 961, unify on (0).2 in 961 and (0).2.1 in 961
  have eq1100 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1020 eq9 -- backward demodulation 9,1020
  have eq1143 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1100 eq12 -- backward demodulation 12,1100
  have eq1197 : sK0 ≠ sK0 := superpose eq1143 eq13 -- superposition 13,1143, 1143 into 13, unify on (0).2 in 1143 and (0).2 in 13
  subsumption eq1197 rfl


@[equational_result]
theorem Equation2720_implies_Equation3702 (G : Type*) [Magma G] (h : Equation2720 G) : Equation3702 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1323 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK0)) := superpose eq1260 eq10 -- backward demodulation 10,1260
  have eq1324 : sK0 ≠ ((sK1 ◇ sK2) ◇ sK0) := superpose eq1260 eq1323 -- forward demodulation 1323,1260
  subsumption eq1324 eq1260


@[equational_result]
theorem Equation2720_implies_Equation2855 (G : Type*) [Magma G] (h : Equation2720 G) : Equation2855 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1321 : sK0 ≠ (sK1 ◇ sK0) := superpose eq1217 eq10 -- backward demodulation 10,1217
  subsumption eq1321 eq1260


@[equational_result]
theorem Equation2720_implies_Equation3474 (G : Type*) [Magma G] (h : Equation2720 G) : Equation3474 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq223 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq43 eq10 -- superposition 10,43, 43 into 10, unify on (0).2 in 43 and (0).2 in 10
  have eq892 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq956 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq892 -- forward demodulation 892,12
  have eq1015 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq956 eq956 -- superposition 956,956, 956 into 956, unify on (0).2 in 956 and (0).2.1 in 956
  have eq1095 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1015 eq9 -- backward demodulation 9,1015
  have eq1138 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1095 eq12 -- backward demodulation 12,1095
  have eq1193 : sK0 ≠ (sK0 ◇ sK0) := superpose eq1095 eq223 -- backward demodulation 223,1095
  subsumption eq1193 eq1138


@[equational_result]
theorem Equation2720_implies_Equation2351 (G : Type*) [Magma G] (h : Equation2720 G) : Equation2351 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1323 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK0) := superpose eq1260 eq10 -- backward demodulation 10,1260
  subsumption eq1323 eq1260


@[equational_result]
theorem Equation2720_implies_Equation4428 (G : Type*) [Magma G] (h : Equation2720 G) : Equation4428 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ sK1) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1321 : sK1 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq1217 eq10 -- backward demodulation 10,1217
  have eq1324 : sK1 ≠ (sK0 ◇ sK1) := superpose eq1260 eq1321 -- forward demodulation 1321,1260
  subsumption eq1324 eq1260


@[equational_result]
theorem Equation2720_implies_Equation329 (G : Type*) [Magma G] (h : Equation2720 G) : Equation329 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1323 : sK1 ≠ (sK0 ◇ (sK2 ◇ sK1)) := superpose eq1260 eq10 -- backward demodulation 10,1260
  have eq1324 : sK1 ≠ (sK0 ◇ sK1) := superpose eq1260 eq1323 -- forward demodulation 1323,1260
  subsumption eq1324 eq1260


@[equational_result]
theorem Equation2720_implies_Equation2905 (G : Type*) [Magma G] (h : Equation2720 G) : Equation2905 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1321 : sK0 ≠ (sK2 ◇ sK0) := superpose eq1217 eq10 -- backward demodulation 10,1217
  subsumption eq1321 eq1260


@[equational_result]
theorem Equation2720_implies_Equation2894 (G : Type*) [Magma G] (h : Equation2720 G) : Equation2894 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK3) ◇ sK0) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1321 : sK0 ≠ (sK3 ◇ sK0) := superpose eq1217 eq10 -- backward demodulation 10,1217
  subsumption eq1321 eq1260


@[equational_result]
theorem Equation2720_implies_Equation3081 (G : Type*) [Magma G] (h : Equation2720 G) : Equation3081 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 : sK0 ≠ (sK2 ◇ sK0) := superpose eq1217 eq10 -- backward demodulation 10,1217
  have eq1261 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1324 : sK0 ≠ sK0 := superpose eq1261 eq1260 -- superposition 1260,1261, 1261 into 1260, unify on (0).2 in 1261 and (0).2 in 1260
  subsumption eq1324 rfl


@[equational_result]
theorem Equation2720_implies_Equation3798 (G : Type*) [Magma G] (h : Equation2720 G) : Equation3798 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK0) ◇ (sK3 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1323 : sK1 ≠ ((sK2 ◇ sK0) ◇ (sK3 ◇ sK1)) := superpose eq1260 eq10 -- backward demodulation 10,1260
  have eq1324 : sK1 ≠ ((sK2 ◇ sK0) ◇ sK1) := superpose eq1260 eq1323 -- forward demodulation 1323,1260
  subsumption eq1324 eq1260


@[equational_result]
theorem Equation2720_implies_Equation312 (G : Type*) [Magma G] (h : Equation2720 G) : Equation312 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1323 : sK0 ≠ (sK1 ◇ sK0) := superpose eq1260 eq10 -- backward demodulation 10,1260
  subsumption eq1323 eq1260


@[equational_result]
theorem Equation2720_implies_Equation3654 (G : Type*) [Magma G] (h : Equation2720 G) : Equation3654 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK3 ◇ sK4) ◇ sK1)) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1321 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK1) := superpose eq1217 eq10 -- backward demodulation 10,1217
  have eq1324 : sK1 ≠ (sK0 ◇ sK1) := superpose eq1260 eq1321 -- forward demodulation 1321,1260
  subsumption eq1324 eq1260


@[equational_result]
theorem Equation2720_implies_Equation2912 (G : Type*) [Magma G] (h : Equation2720 G) : Equation2912 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1321 : sK0 ≠ (sK1 ◇ sK0) := superpose eq1217 eq10 -- backward demodulation 10,1217
  subsumption eq1321 eq1260


@[equational_result]
theorem Equation2720_implies_Equation3706 (G : Type*) [Magma G] (h : Equation2720 G) : Equation3706 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1323 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK0)) := superpose eq1260 eq10 -- backward demodulation 10,1260
  have eq1324 : sK0 ≠ ((sK1 ◇ sK2) ◇ sK0) := superpose eq1260 eq1323 -- forward demodulation 1323,1260
  subsumption eq1324 eq1260


@[equational_result]
theorem Equation2720_implies_Equation3549 (G : Type*) [Magma G] (h : Equation2720 G) : Equation3549 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1321 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq1217 eq10 -- backward demodulation 10,1217
  have eq1324 : sK1 ≠ (sK0 ◇ sK1) := superpose eq1260 eq1321 -- forward demodulation 1321,1260
  subsumption eq1324 eq1260


@[equational_result]
theorem Equation2720_implies_Equation3471 (G : Type*) [Magma G] (h : Equation2720 G) : Equation3471 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1321 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq1217 eq10 -- backward demodulation 10,1217
  have eq1324 : sK0 ≠ (sK0 ◇ sK0) := superpose eq1260 eq1321 -- forward demodulation 1321,1260
  subsumption eq1324 eq1260


@[equational_result]
theorem Equation2720_implies_Equation3698 (G : Type*) [Magma G] (h : Equation2720 G) : Equation3698 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1323 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK0)) := superpose eq1260 eq10 -- backward demodulation 10,1260
  have eq1324 : sK0 ≠ ((sK1 ◇ sK2) ◇ sK0) := superpose eq1260 eq1323 -- forward demodulation 1323,1260
  subsumption eq1324 eq1260


@[equational_result]
theorem Equation2720_implies_Equation3744 (G : Type*) [Magma G] (h : Equation2720 G) : Equation3744 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ (sK3 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1323 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ sK1)) := superpose eq1260 eq10 -- backward demodulation 10,1260
  have eq1324 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK1) := superpose eq1260 eq1323 -- forward demodulation 1323,1260
  have eq1325 : sK1 ≠ (sK0 ◇ sK1) := superpose eq1260 eq1324 -- forward demodulation 1324,1260
  subsumption eq1325 eq1260


@[equational_result]
theorem Equation2720_implies_Equation3130 (G : Type*) [Magma G] (h : Equation2720 G) : Equation3130 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK2) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 : sK0 ≠ (sK2 ◇ sK0) := superpose eq1217 eq10 -- backward demodulation 10,1217
  have eq1261 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1324 : sK0 ≠ sK0 := superpose eq1261 eq1260 -- superposition 1260,1261, 1261 into 1260, unify on (0).2 in 1261 and (0).2 in 1260
  subsumption eq1324 rfl


@[equational_result]
theorem Equation2720_implies_Equation2385 (G : Type*) [Magma G] (h : Equation2720 G) : Equation2385 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1323 : sK0 ≠ ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK0) := superpose eq1260 eq10 -- backward demodulation 10,1260
  subsumption eq1323 eq1260


@[equational_result]
theorem Equation2720_implies_Equation4498 (G : Type*) [Magma G] (h : Equation2720 G) : Equation4498 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1321 : sK1 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq1217 eq10 -- backward demodulation 10,1217
  have eq1324 : sK1 ≠ (sK0 ◇ sK1) := superpose eq1260 eq1321 -- forward demodulation 1321,1260
  subsumption eq1324 eq1260


@[equational_result]
theorem Equation2720_implies_Equation3670 (G : Type*) [Magma G] (h : Equation2720 G) : Equation3670 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1323 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq1260 eq10 -- backward demodulation 10,1260
  have eq1324 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq1260 eq1323 -- forward demodulation 1323,1260
  have eq1325 : sK0 ≠ (sK0 ◇ sK0) := superpose eq1260 eq1324 -- forward demodulation 1324,1260
  subsumption eq1325 eq1260


@[equational_result]
theorem Equation2720_implies_Equation3481 (G : Type*) [Magma G] (h : Equation2720 G) : Equation3481 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1321 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq1217 eq10 -- backward demodulation 10,1217
  have eq1324 : sK0 ≠ (sK0 ◇ sK0) := superpose eq1260 eq1321 -- forward demodulation 1321,1260
  subsumption eq1324 eq1260


@[equational_result]
theorem Equation2720_implies_Equation2939 (G : Type*) [Magma G] (h : Equation2720 G) : Equation2939 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq209 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = X1 := superpose eq43 eq9 -- superposition 9,43, 43 into 9, unify on (0).2 in 43 and (0).1.1 in 9
  have eq307 : sK0 ≠ sK0 := superpose eq209 eq10 -- superposition 10,209, 209 into 10, unify on (0).2 in 209 and (0).2 in 10
  subsumption eq307 rfl


@[equational_result]
theorem Equation2720_implies_Equation3467 (G : Type*) [Magma G] (h : Equation2720 G) : Equation3467 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1321 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq1217 eq10 -- backward demodulation 10,1217
  subsumption eq1321 rfl


@[equational_result]
theorem Equation2720_implies_Equation2389 (G : Type*) [Magma G] (h : Equation2720 G) : Equation2389 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1323 : sK0 ≠ ((sK2 ◇ (sK1 ◇ sK2)) ◇ sK0) := superpose eq1260 eq10 -- backward demodulation 10,1260
  subsumption eq1323 eq1260


@[equational_result]
theorem Equation2720_implies_Equation3736 (G : Type*) [Magma G] (h : Equation2720 G) : Equation3736 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1323 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ sK1)) := superpose eq1260 eq10 -- backward demodulation 10,1260
  have eq1324 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK1) := superpose eq1260 eq1323 -- forward demodulation 1323,1260
  have eq1325 : sK1 ≠ (sK0 ◇ sK1) := superpose eq1260 eq1324 -- forward demodulation 1324,1260
  subsumption eq1325 eq1260


@[equational_result]
theorem Equation2720_implies_Equation3495 (G : Type*) [Magma G] (h : Equation2720 G) : Equation3495 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1321 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq1217 eq10 -- backward demodulation 10,1217
  have eq1324 : sK0 ≠ (sK0 ◇ sK0) := superpose eq1260 eq1321 -- forward demodulation 1321,1260
  subsumption eq1324 eq1260


@[equational_result]
theorem Equation2720_implies_Equation2402 (G : Type*) [Magma G] (h : Equation2720 G) : Equation2402 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1323 : sK0 ≠ ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK0) := superpose eq1260 eq10 -- backward demodulation 10,1260
  subsumption eq1323 eq1260


@[equational_result]
theorem Equation2720_implies_Equation2915 (G : Type*) [Magma G] (h : Equation2720 G) : Equation2915 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1321 : sK0 ≠ (sK2 ◇ sK0) := superpose eq1217 eq10 -- backward demodulation 10,1217
  subsumption eq1321 eq1260


@[equational_result]
theorem Equation2720_implies_Equation309 (G : Type*) [Magma G] (h : Equation2720 G) : Equation309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1323 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq1260 eq10 -- backward demodulation 10,1260
  have eq1324 : sK0 ≠ (sK0 ◇ sK0) := superpose eq1260 eq1323 -- forward demodulation 1323,1260
  subsumption eq1324 eq1260


@[equational_result]
theorem Equation2720_implies_Equation273 (G : Type*) [Magma G] (h : Equation2720 G) : Equation273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2720_implies_Equation1767 (G : Type*) [Magma G] (h : Equation2720 G) : Equation1767 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK3) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1321 : sK0 ≠ ((sK1 ◇ sK2) ◇ sK0) := superpose eq1217 eq10 -- backward demodulation 10,1217
  subsumption eq1321 eq1260


@[equational_result]
theorem Equation1485_implies_Equation2162 (G : Type*) [Magma G] (h : Equation1485 G) : Equation2162 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X3 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ X4) ◇ (X4 ◇ X3)) = X4 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1.2 in 12
  have eq50 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1485_implies_Equation2035 (G : Type*) [Magma G] (h : Equation1485 G) : Equation2035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X3 ◇ X1)) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq13 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ X4) ◇ (X4 ◇ X3)) = X4 := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1.1.1.2 in 11
  have eq49 : sK0 ≠ sK0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2 in 9
  subsumption eq49 rfl


@[equational_result]
theorem Equation1485_implies_Equation2050 (G : Type*) [Magma G] (h : Equation1485 G) : Equation2050 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X3 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ X4) ◇ (X4 ◇ X3)) = X4 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1.2 in 12
  have eq50 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1485_implies_Equation2125 (G : Type*) [Magma G] (h : Equation1485 G) : Equation2125 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X3 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ X4) ◇ (X4 ◇ X3)) = X4 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1.2 in 12
  have eq50 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1485_implies_Equation2088 (G : Type*) [Magma G] (h : Equation1485 G) : Equation2088 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X3 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ X4) ◇ (X4 ◇ X3)) = X4 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1.2 in 12
  have eq50 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation2162_implies_Equation1485 (G : Type*) [Magma G] (h : Equation2162 G) : Equation1485 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X2 X3 X4 : G) : ((X3 ◇ X4) ◇ (X4 ◇ (X2 ◇ X3))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.1 in 11
  have eq50 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation2162_implies_Equation1482 (G : Type*) [Magma G] (h : Equation2162 G) : Equation1482 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X2 X3 X4 : G) : ((X3 ◇ X4) ◇ (X4 ◇ (X2 ◇ X3))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.1 in 11
  have eq50 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation2162_implies_Equation1479 (G : Type*) [Magma G] (h : Equation2162 G) : Equation1479 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X2 X3 X4 : G) : ((X3 ◇ X4) ◇ (X4 ◇ (X2 ◇ X3))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.1 in 11
  have eq50 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation2162_implies_Equation1428 (G : Type*) [Magma G] (h : Equation2162 G) : Equation1428 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X2 X3 X4 : G) : ((X3 ◇ X4) ◇ (X4 ◇ (X2 ◇ X3))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.1 in 11
  have eq50 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1101_implies_Equation2725 (G : Type*) [Magma G] (h : Equation1101 G) : Equation2725 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK2 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X3)) = ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq26 (X0 : G) : sK0 ≠ ((X0 ◇ ((sK1 ◇ sK0) ◇ X0)) ◇ sK1) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2.1 in 10
  have eq1267 (X0 X1 : G) : sK0 ≠ (((sK1 ◇ (X0 ◇ X0)) ◇ (sK0 ◇ (X1 ◇ X1))) ◇ sK1) := superpose eq19 eq26 -- superposition 26,19, 19 into 26, unify on (0).2 in 19 and (0).2.1.2 in 26
  subsumption eq1267 eq12


@[equational_result]
theorem Equation1101_implies_Equation3662 (G : Type*) [Magma G] (h : Equation1101 G) : Equation3662 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq27 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq31 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X0 := superpose eq9 eq27 -- forward demodulation 27,9
  have eq32 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq31 eq26 -- backward demodulation 26,31
  subsumption eq32 rfl


@[equational_result]
theorem Equation1101_implies_Equation2543 (G : Type*) [Magma G] (h : Equation1101 G) : Equation2543 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq26 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq30 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X0 := superpose eq9 eq26 -- forward demodulation 26,9
  have eq33 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq30 eq10 -- backward demodulation 10,30
  subsumption eq33 eq30


@[equational_result]
theorem Equation1101_implies_Equation3058 (G : Type*) [Magma G] (h : Equation1101 G) : Equation3058 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq23 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq30 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X0 := superpose eq9 eq23 -- forward demodulation 23,9
  have eq32 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq30 eq10 -- backward demodulation 10,30
  subsumption eq32 eq30


@[equational_result]
theorem Equation1101_implies_Equation1746 (G : Type*) [Magma G] (h : Equation1101 G) : Equation1746 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq26 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq30 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X0 := superpose eq9 eq26 -- forward demodulation 26,9
  have eq33 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq30 eq10 -- backward demodulation 10,30
  subsumption eq33 eq30


@[equational_result]
theorem Equation1101_implies_Equation2710 (G : Type*) [Magma G] (h : Equation1101 G) : Equation2710 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X3)) = ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq23 (X0 : G) : sK0 ≠ ((X0 ◇ ((sK1 ◇ sK0) ◇ X0)) ◇ sK1) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2.1 in 10
  have eq1267 (X0 X1 : G) : sK0 ≠ (((sK1 ◇ (X0 ◇ X0)) ◇ (sK0 ◇ (X1 ◇ X1))) ◇ sK1) := superpose eq19 eq23 -- superposition 23,19, 19 into 23, unify on (0).2 in 19 and (0).2.1.2 in 23
  subsumption eq1267 eq12


@[equational_result]
theorem Equation1101_implies_Equation4068 (G : Type*) [Magma G] (h : Equation1101 G) : Equation4068 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq23 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq30 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X0 := superpose eq9 eq23 -- forward demodulation 23,9
  have eq32 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq30 eq10 -- backward demodulation 10,30
  have eq37 (X0 X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq11 eq30 -- superposition 30,11, 11 into 30, unify on (0).2 in 11 and (0).1 in 30
  have eq48 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq30 eq37 -- forward demodulation 37,30
  have eq110 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq48 eq32 -- superposition 32,48, 48 into 32, unify on (0).2 in 48 and (0).2 in 32
  subsumption eq110 eq48


@[equational_result]
theorem Equation1101_implies_Equation2697 (G : Type*) [Magma G] (h : Equation1101 G) : Equation2697 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X3)) = ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq23 (X0 : G) : sK0 ≠ ((X0 ◇ ((sK1 ◇ sK0) ◇ X0)) ◇ sK1) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2.1 in 10
  have eq1285 (X0 X1 : G) : sK0 ≠ (((sK1 ◇ (X0 ◇ X0)) ◇ (sK0 ◇ (X1 ◇ X1))) ◇ sK1) := superpose eq19 eq23 -- superposition 23,19, 19 into 23, unify on (0).2 in 19 and (0).2.1.2 in 23
  subsumption eq1285 eq12


@[equational_result]
theorem Equation1101_implies_Equation4090 (G : Type*) [Magma G] (h : Equation1101 G) : Equation4090 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq23 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq30 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X0 := superpose eq9 eq23 -- forward demodulation 23,9
  have eq32 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq30 eq10 -- backward demodulation 10,30
  subsumption eq32 rfl


@[equational_result]
theorem Equation1101_implies_Equation3472 (G : Type*) [Magma G] (h : Equation1101 G) : Equation3472 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq26 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq30 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X0 := superpose eq9 eq26 -- forward demodulation 26,9
  have eq33 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq30 eq10 -- backward demodulation 10,30
  have eq37 (X0 X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq11 eq30 -- superposition 30,11, 11 into 30, unify on (0).2 in 11 and (0).1 in 30
  have eq48 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq30 eq37 -- forward demodulation 37,30
  have eq110 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq48 eq33 -- superposition 33,48, 48 into 33, unify on (0).2 in 48 and (0).2 in 33
  subsumption eq110 eq48


@[equational_result]
theorem Equation1101_implies_Equation2644 (G : Type*) [Magma G] (h : Equation1101 G) : Equation2644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq23 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3))) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2 in 8
  have eq30 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X0 := superpose eq8 eq23 -- forward demodulation 23,8
  have eq32 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq30 eq9 -- backward demodulation 9,30
  subsumption eq32 eq30


@[equational_result]
theorem Equation1101_implies_Equation3522 (G : Type*) [Magma G] (h : Equation1101 G) : Equation3522 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq26 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq30 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X0 := superpose eq9 eq26 -- forward demodulation 26,9
  have eq33 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq30 eq10 -- backward demodulation 10,30
  subsumption eq33 rfl


@[equational_result]
theorem Equation1101_implies_Equation2746 (G : Type*) [Magma G] (h : Equation1101 G) : Equation2746 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq24 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq31 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X0 := superpose eq9 eq24 -- forward demodulation 24,9
  have eq33 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq31 eq10 -- backward demodulation 10,31
  subsumption eq33 eq31


@[equational_result]
theorem Equation1101_implies_Equation3759 (G : Type*) [Magma G] (h : Equation1101 G) : Equation3759 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq26 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq30 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X0 := superpose eq9 eq26 -- forward demodulation 26,9
  have eq75 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq30 eq10 -- superposition 10,30, 30 into 10, unify on (0).2 in 30 and (0).2 in 10
  subsumption eq75 rfl


@[equational_result]
theorem Equation1101_implies_Equation3456 (G : Type*) [Magma G] (h : Equation1101 G) : Equation3456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq25 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3))) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2 in 8
  have eq29 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X0 := superpose eq8 eq25 -- forward demodulation 25,8
  have eq32 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq29 eq9 -- backward demodulation 9,29
  subsumption eq32 rfl


@[equational_result]
theorem Equation1101_implies_Equation3820 (G : Type*) [Magma G] (h : Equation1101 G) : Equation3820 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq26 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq30 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X0 := superpose eq9 eq26 -- forward demodulation 26,9
  have eq70 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq30 eq10 -- superposition 10,30, 30 into 10, unify on (0).2 in 30 and (0).2 in 10
  subsumption eq70 rfl


@[equational_result]
theorem Equation1101_implies_Equation2466 (G : Type*) [Magma G] (h : Equation1101 G) : Equation2466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq26 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq30 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X0 := superpose eq9 eq26 -- forward demodulation 26,9
  have eq33 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq30 eq10 -- backward demodulation 10,30
  subsumption eq33 eq30


@[equational_result]
theorem Equation2725_implies_Equation1101 (G : Type*) [Magma G] (h : Equation2725 G) : Equation1101 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq19 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X3 ◇ X3)) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq24 (X0 X3 : G) : ((X3 ◇ X3) ◇ X0) = X0 := superpose eq21 eq19 -- backward demodulation 19,21
  have eq35 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X3))) = X2 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq37 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = ((X0 ◇ (X3 ◇ X3)) ◇ (X1 ◇ (X4 ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq51 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X1) ◇ (X3 ◇ X3))) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.2.1 in 11
  have eq59 (X0 : G) : sK0 ≠ (sK1 ◇ ((sK0 ◇ (X0 ◇ X0)) ◇ sK1)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2.1.2 in 10
  have eq69 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) = X0 := superpose eq24 eq51 -- forward demodulation 51,24
  have eq540 (X0 X1 X2 X4 X5 : G) : (X1 ◇ ((X0 ◇ (X4 ◇ X4)) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X5 ◇ X5)))) = X0 := superpose eq37 eq35 -- superposition 35,37, 37 into 35, unify on (0).2 in 37 and (0).1.2 in 35
  have eq666 (X0 X1 X4 : G) : (X1 ◇ ((X0 ◇ (X4 ◇ X4)) ◇ X1)) = X0 := superpose eq69 eq540 -- forward demodulation 540,69
  have eq1299 : sK0 ≠ sK0 := superpose eq666 eq59 -- superposition 59,666, 666 into 59, unify on (0).2 in 666 and (0).2 in 59
  subsumption eq1299 rfl


