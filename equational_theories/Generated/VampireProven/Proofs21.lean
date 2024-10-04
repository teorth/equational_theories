import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation662_implies_Equation362 (G : Type*) [Magma G] (h : Equation662 G) : Equation362 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X5))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq14 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0)) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq16 eq14 -- backward demodulation 14,16
  have eq25 (X4 X5 : G) : (X4 ◇ X5) = X4 := superpose eq21 eq11 -- backward demodulation 11,21
  have eq29 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq25 eq10 -- backward demodulation 10,25
  have eq30 : sK0 ≠ (sK0 ◇ sK1) := superpose eq25 eq29 -- forward demodulation 29,25
  subsumption eq30 eq25


@[equational_result]
theorem Equation662_implies_Equation417 (G : Type*) [Magma G] (h : Equation662 G) : Equation417 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X5))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq15 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0)) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq22 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq17 eq15 -- backward demodulation 15,17
  have eq26 (X4 X5 : G) : (X4 ◇ X5) = X4 := superpose eq22 eq11 -- backward demodulation 11,22
  have eq30 : sK0 ≠ sK0 := superpose eq26 eq14 -- superposition 14,26, 26 into 14, unify on (0).2 in 26 and (0).2 in 14
  subsumption eq30 rfl


@[equational_result]
theorem Equation662_implies_Equation2250 (G : Type*) [Magma G] (h : Equation662 G) : Equation2250 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK1) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X5))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq14 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0)) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq16 eq14 -- backward demodulation 14,16
  have eq25 (X4 X5 : G) : (X4 ◇ X5) = X4 := superpose eq21 eq11 -- backward demodulation 11,21
  have eq26 : sK0 ≠ (sK0 ◇ sK1) := superpose eq21 eq10 -- backward demodulation 10,21
  subsumption eq26 eq25


@[equational_result]
theorem Equation662_implies_Equation3747 (G : Type*) [Magma G] (h : Equation662 G) : Equation3747 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ (sK3 ◇ sK4)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X5))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq14 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0)) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq16 eq14 -- backward demodulation 14,16
  have eq25 (X4 X5 : G) : (X4 ◇ X5) = X4 := superpose eq21 eq11 -- backward demodulation 11,21
  have eq29 : sK0 ≠ ((sK0 ◇ sK2) ◇ (sK3 ◇ sK4)) := superpose eq25 eq10 -- backward demodulation 10,25
  have eq30 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK3) := superpose eq25 eq29 -- forward demodulation 29,25
  have eq31 : sK0 ≠ (sK0 ◇ sK3) := superpose eq25 eq30 -- forward demodulation 30,25
  subsumption eq31 eq25


@[equational_result]
theorem Equation662_implies_Equation3927 (G : Type*) [Magma G] (h : Equation662 G) : Equation3927 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X5))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq14 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0)) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq16 eq14 -- backward demodulation 14,16
  have eq25 (X4 X5 : G) : (X4 ◇ X5) = X4 := superpose eq21 eq11 -- backward demodulation 11,21
  have eq26 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq21 eq10 -- backward demodulation 10,21
  have eq30 : sK0 ≠ (sK0 ◇ sK1) := superpose eq25 eq26 -- forward demodulation 26,25
  subsumption eq30 eq25


@[equational_result]
theorem Equation662_implies_Equation429 (G : Type*) [Magma G] (h : Equation662 G) : Equation429 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X5))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK1) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq15 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0)) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq22 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq17 eq15 -- backward demodulation 15,17
  have eq26 (X4 X5 : G) : (X4 ◇ X5) = X4 := superpose eq22 eq11 -- backward demodulation 11,22
  have eq30 : sK0 ≠ sK0 := superpose eq26 eq14 -- superposition 14,26, 26 into 14, unify on (0).2 in 26 and (0).2 in 14
  subsumption eq30 rfl


@[equational_result]
theorem Equation662_implies_Equation1054 (G : Type*) [Magma G] (h : Equation662 G) : Equation1054 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK3)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X5))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq14 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0)) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq16 eq14 -- backward demodulation 14,16
  have eq25 (X4 X5 : G) : (X4 ◇ X5) = X4 := superpose eq21 eq11 -- backward demodulation 11,21
  have eq27 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK3)) := superpose eq21 eq10 -- backward demodulation 10,21
  subsumption eq27 eq25


@[equational_result]
theorem Equation662_implies_Equation4475 (G : Type*) [Magma G] (h : Equation662 G) : Equation4475 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X5))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq14 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0)) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq16 eq14 -- backward demodulation 14,16
  have eq25 (X4 X5 : G) : (X4 ◇ X5) = X4 := superpose eq21 eq11 -- backward demodulation 11,21
  have eq26 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK0) := superpose eq21 eq10 -- backward demodulation 10,21
  have eq30 : sK0 ≠ (sK0 ◇ sK0) := superpose eq25 eq26 -- forward demodulation 26,25
  subsumption eq30 eq25


@[equational_result]
theorem Equation479_implies_Equation4611 (G : Type*) [Magma G] (h : Equation479 G) : Equation4611 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : ((sK0 ◇ sK0) ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation479_implies_Equation3918 (G : Type*) [Magma G] (h : Equation479 G) : Equation3918 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq16 eq13


@[equational_result]
theorem Equation479_implies_Equation361 (G : Type*) [Magma G] (h : Equation479 G) : Equation361 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation479_implies_Equation4243 (G : Type*) [Magma G] (h : Equation479 G) : Equation4243 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK3) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq21 (X0 : G) : (sK0 ◇ sK1) ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).2.1 in 15
  subsumption eq21 eq16


@[equational_result]
theorem Equation479_implies_Equation603 (G : Type*) [Magma G] (h : Equation479 G) : Equation603 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = (X3 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq13 eq12 -- backward demodulation 12,13
  have eq15 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq35 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).1.2 in 9
  have eq39 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2 in 15
  have eq98 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2)))) = (X4 ◇ (((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ (X4 ◇ (X1 ◇ X2)))) := superpose eq14 eq11 -- superposition 11,14, 14 into 11, unify on (0).2 in 14 and (0).1.2.2 in 11
  have eq143 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2)))) = X2 := superpose eq35 eq98 -- forward demodulation 98,35
  have eq336 : sK0 ≠ sK0 := superpose eq143 eq39 -- superposition 39,143, 143 into 39, unify on (0).2 in 143 and (0).2 in 39
  subsumption eq336 rfl


@[equational_result]
theorem Equation479_implies_Equation3877 (G : Type*) [Magma G] (h : Equation479 G) : Equation3877 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation479_implies_Equation4291 (G : Type*) [Magma G] (h : Equation479 G) : Equation4291 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq55 (X0 : G) : (sK0 ◇ (X0 ◇ sK1)) ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).1.2 in 10
  subsumption eq55 eq15


@[equational_result]
theorem Equation479_implies_Equation3997 (G : Type*) [Magma G] (h : Equation479 G) : Equation3997 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK0 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 eq13


@[equational_result]
theorem Equation469_implies_Equation603 (G : Type*) [Magma G] (h : Equation469 G) : Equation603 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) = (X3 ◇ (((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq21 (X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) = (X3 ◇ X1) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq69 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq21 eq21 -- superposition 21,21, 21 into 21, unify on (0).2 in 21 and (0).1 in 21
  have eq170 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq69 eq9 -- superposition 9,69, 69 into 9, unify on (0).2 in 69 and (0).1.2 in 9
  have eq178 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (X0 ◇ sK0)))) := superpose eq69 eq10 -- superposition 10,69, 69 into 10, unify on (0).2 in 69 and (0).2.2.2.2 in 10
  have eq495 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (X0 ◇ sK0)))) := superpose eq12 eq178 -- superposition 178,12, 12 into 178, unify on (0).2 in 12 and (0).2.2.2 in 178
  subsumption eq495 eq170


@[equational_result]
theorem Equation469_implies_Equation4118 (G : Type*) [Magma G] (h : Equation469 G) : Equation4118 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) = (X3 ◇ (((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq21 (X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) = (X3 ◇ X1) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq69 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq21 eq21 -- superposition 21,21, 21 into 21, unify on (0).2 in 21 and (0).1 in 21
  have eq176 (X0 : G) : (sK0 ◇ sK1) ≠ (((X0 ◇ sK0) ◇ sK0) ◇ sK1) := superpose eq69 eq10 -- superposition 10,69, 69 into 10, unify on (0).2 in 69 and (0).2.1.1 in 10
  subsumption eq176 eq69


@[equational_result]
theorem Equation469_implies_Equation3862 (G : Type*) [Magma G] (h : Equation469 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq12 (X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) = (X3 ◇ (((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1.2 in 11
  have eq20 (X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) = (X3 ◇ X1) := superpose eq8 eq12 -- forward demodulation 12,8
  have eq68 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq20 eq20 -- superposition 20,20, 20 into 20, unify on (0).2 in 20 and (0).1 in 20
  have eq156 (X0 : G) : (X0 ◇ sK0) ≠ ((sK0 ◇ (X0 ◇ sK0)) ◇ sK0) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1 in 9
  subsumption eq156 eq68


@[equational_result]
theorem Equation469_implies_Equation532 (G : Type*) [Magma G] (h : Equation469 G) : Equation532 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X1))) = (X3 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) = (X3 ◇ (((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq21 (X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) = (X3 ◇ X1) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq65 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) = (X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).1.1.2 in 21
  have eq69 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq21 eq21 -- superposition 21,21, 21 into 21, unify on (0).2 in 21 and (0).1 in 21
  have eq94 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) = (X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := superpose eq9 eq65 -- forward demodulation 65,9
  have eq97 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X1))) = (X3 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1))) := superpose eq94 eq11 -- backward demodulation 11,94
  have eq112 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X3 ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq21 eq97 -- superposition 97,21, 21 into 97, unify on (0).2 in 21 and (0).2.2.2 in 97
  have eq178 (X0 : G) : sK0 ≠ (sK1 ◇ (sK1 ◇ (X0 ◇ (sK3 ◇ sK0)))) := superpose eq69 eq10 -- superposition 10,69, 69 into 10, unify on (0).2 in 69 and (0).2.2.2 in 10
  have eq497 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (X0 ◇ sK0)))) := superpose eq112 eq178 -- superposition 178,112, 112 into 178, unify on (0).2 in 112 and (0).2.2 in 178
  subsumption eq497 eq9


@[equational_result]
theorem Equation1054_implies_Equation4513 (G : Type*) [Magma G] (h : Equation1054 G) : Equation4513 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK1) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ (X0 ◇ (X0 ◇ X1))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq38 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK1) := superpose eq26 eq10 -- backward demodulation 10,26
  have eq39 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq26 eq38 -- forward demodulation 38,26
  subsumption eq39 eq26


@[equational_result]
theorem Equation1054_implies_Equation4070 (G : Type*) [Magma G] (h : Equation1054 G) : Equation4070 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ (X0 ◇ (X0 ◇ X1))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq38 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq26 eq10 -- backward demodulation 10,26
  have eq39 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq26 eq38 -- forward demodulation 38,26
  subsumption eq39 rfl


@[equational_result]
theorem Equation1054_implies_Equation1852 (G : Type*) [Magma G] (h : Equation1054 G) : Equation1852 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ (X0 ◇ (X0 ◇ X1))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq38 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq26 eq10 -- backward demodulation 10,26
  subsumption eq38 eq26


@[equational_result]
theorem Equation1054_implies_Equation4130 (G : Type*) [Magma G] (h : Equation1054 G) : Equation4130 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ (X0 ◇ (X0 ◇ X1))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq38 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq26 eq10 -- backward demodulation 10,26
  subsumption eq38 eq26


@[equational_result]
theorem Equation1054_implies_Equation4121 (G : Type*) [Magma G] (h : Equation1054 G) : Equation4121 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ (X0 ◇ (X0 ◇ X1))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq38 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq26 eq10 -- backward demodulation 10,26
  have eq39 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq26 eq38 -- forward demodulation 38,26
  have eq40 : sK0 ≠ (sK0 ◇ sK1) := superpose eq26 eq39 -- forward demodulation 39,26
  subsumption eq40 eq26


@[equational_result]
theorem Equation1054_implies_Equation3097 (G : Type*) [Magma G] (h : Equation1054 G) : Equation3097 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK3) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ (X0 ◇ (X0 ◇ X1))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq38 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK3) ◇ sK0) := superpose eq26 eq10 -- backward demodulation 10,26
  have eq39 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq26 eq38 -- forward demodulation 38,26
  have eq40 : sK0 ≠ (sK0 ◇ sK0) := superpose eq26 eq39 -- forward demodulation 39,26
  subsumption eq40 eq26


@[equational_result]
theorem Equation1054_implies_Equation837 (G : Type*) [Magma G] (h : Equation1054 G) : Equation837 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ (X0 ◇ (X0 ◇ X1))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq38 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq26 eq10 -- backward demodulation 10,26
  subsumption eq38 eq26


@[equational_result]
theorem Equation1054_implies_Equation1233 (G : Type*) [Magma G] (h : Equation1054 G) : Equation1233 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ (X0 ◇ (X0 ◇ X1))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq38 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := superpose eq26 eq10 -- backward demodulation 10,26
  subsumption eq38 eq26


@[equational_result]
theorem Equation1054_implies_Equation3661 (G : Type*) [Magma G] (h : Equation1054 G) : Equation3661 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ (X0 ◇ (X0 ◇ X1))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq38 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq26 eq10 -- backward demodulation 10,26
  subsumption eq38 eq26


@[equational_result]
theorem Equation1054_implies_Equation2254 (G : Type*) [Magma G] (h : Equation1054 G) : Equation2254 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X0 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq13 (X0 X1 X5 : G) : (X5 ◇ (X0 ◇ (X0 ◇ X1))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X4 : G) : (X4 ◇ (X0 ◇ X0)) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq16 eq10 -- backward demodulation 10,16
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X1 := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).1.2.1 in 9
  have eq31 (X0 X5 : G) : (X5 ◇ X0) = X5 := superpose eq25 eq13 -- backward demodulation 13,25
  have eq37 : sK0 ≠ (sK0 ◇ sK1) := superpose eq31 eq21 -- backward demodulation 21,31
  subsumption eq37 eq31


@[equational_result]
theorem Equation1054_implies_Equation1879 (G : Type*) [Magma G] (h : Equation1054 G) : Equation1879 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ (X0 ◇ (X0 ◇ X1))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq38 : sK0 ≠ (sK0 ◇ (sK3 ◇ sK0)) := superpose eq26 eq10 -- backward demodulation 10,26
  subsumption eq38 eq26


@[equational_result]
theorem Equation1054_implies_Equation3667 (G : Type*) [Magma G] (h : Equation1054 G) : Equation3667 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ (X0 ◇ (X0 ◇ X1))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq38 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq26 eq10 -- backward demodulation 10,26
  have eq39 : sK0 ≠ (sK0 ◇ sK0) := superpose eq26 eq38 -- forward demodulation 38,26
  subsumption eq39 eq26


@[equational_result]
theorem Equation1054_implies_Equation2893 (G : Type*) [Magma G] (h : Equation1054 G) : Equation2893 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ (X0 ◇ (X0 ◇ X1))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq38 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK3) := superpose eq26 eq10 -- backward demodulation 10,26
  have eq39 : sK0 ≠ (sK0 ◇ sK3) := superpose eq26 eq38 -- forward demodulation 38,26
  subsumption eq39 eq26


@[equational_result]
theorem Equation1054_implies_Equation1258 (G : Type*) [Magma G] (h : Equation1054 G) : Equation1258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ (X0 ◇ (X0 ◇ X1))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq38 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := superpose eq26 eq10 -- backward demodulation 10,26
  subsumption eq38 eq26


@[equational_result]
theorem Equation1054_implies_Equation822 (G : Type*) [Magma G] (h : Equation1054 G) : Equation822 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X0 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq13 (X0 X1 X5 : G) : (X5 ◇ (X0 ◇ (X0 ◇ X1))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X4 : G) : (X4 ◇ (X0 ◇ X0)) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq16 eq10 -- backward demodulation 10,16
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X1 := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).1.2.1 in 9
  have eq31 (X0 X5 : G) : (X5 ◇ X0) = X5 := superpose eq25 eq13 -- backward demodulation 13,25
  have eq37 : sK0 ≠ (sK0 ◇ sK0) := superpose eq31 eq21 -- backward demodulation 21,31
  subsumption eq37 eq31


@[equational_result]
theorem Equation1054_implies_Equation2282 (G : Type*) [Magma G] (h : Equation1054 G) : Equation2282 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK1) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X0 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq13 (X0 X1 X5 : G) : (X5 ◇ (X0 ◇ (X0 ◇ X1))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X4 : G) : (X4 ◇ (X0 ◇ X0)) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq16 eq10 -- backward demodulation 10,16
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X1 := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).1.2.1 in 9
  have eq31 (X0 X5 : G) : (X5 ◇ X0) = X5 := superpose eq25 eq13 -- backward demodulation 13,25
  have eq37 : sK0 ≠ (sK0 ◇ sK1) := superpose eq31 eq21 -- backward demodulation 21,31
  subsumption eq37 eq31


@[equational_result]
theorem Equation1054_implies_Equation1067 (G : Type*) [Magma G] (h : Equation1054 G) : Equation1067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ (X0 ◇ (X0 ◇ X1))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq38 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := superpose eq26 eq10 -- backward demodulation 10,26
  subsumption eq38 eq26


@[equational_result]
theorem Equation1054_implies_Equation1876 (G : Type*) [Magma G] (h : Equation1054 G) : Equation1876 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ (X0 ◇ (X0 ◇ X1))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq38 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK1)) := superpose eq26 eq10 -- backward demodulation 10,26
  subsumption eq38 eq26


@[equational_result]
theorem Equation1054_implies_Equation3868 (G : Type*) [Magma G] (h : Equation1054 G) : Equation3868 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ (X0 ◇ (X0 ◇ X1))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq38 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK1) := superpose eq26 eq10 -- backward demodulation 10,26
  have eq39 : sK0 ≠ (sK0 ◇ sK0) := superpose eq26 eq38 -- forward demodulation 38,26
  subsumption eq39 eq26


@[equational_result]
theorem Equation1054_implies_Equation1447 (G : Type*) [Magma G] (h : Equation1054 G) : Equation1447 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ (X0 ◇ (X0 ◇ X1))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq38 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq26 eq10 -- backward demodulation 10,26
  have eq39 : sK0 ≠ (sK0 ◇ sK0) := superpose eq26 eq38 -- forward demodulation 38,26
  subsumption eq39 eq26


@[equational_result]
theorem Equation1037_implies_Equation1241 (G : Type*) [Magma G] (h : Equation1037 G) : Equation1241 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2 in 12
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq49 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq37 eq27 -- backward demodulation 27,37
  have eq63 : sK0 ≠ sK0 := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2 in 10
  subsumption eq63 rfl


@[equational_result]
theorem Equation1037_implies_Equation1236 (G : Type*) [Magma G] (h : Equation1037 G) : Equation1236 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq19 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2 in 12
  have eq35 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq11 eq19 -- superposition 19,11, 11 into 19, unify on (0).2 in 11 and (0).1.2.1 in 19
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq47 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq37 eq35 -- backward demodulation 35,37
  have eq49 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq37 eq27 -- backward demodulation 27,37
  have eq50 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq37 eq17 -- backward demodulation 17,37
  have eq54 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq49 eq49 -- superposition 49,49, 49 into 49, unify on (0).2 in 49 and (0).1.2 in 49
  have eq63 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := superpose eq54 eq10 -- backward demodulation 10,54
  have eq93 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq47 eq50 -- superposition 50,47, 47 into 50, unify on (0).2 in 47 and (0).1 in 50
  have eq154 : sK0 ≠ sK0 := superpose eq93 eq63 -- superposition 63,93, 93 into 63, unify on (0).2 in 93 and (0).2 in 63
  subsumption eq154 rfl


@[equational_result]
theorem Equation1037_implies_Equation1051 (G : Type*) [Magma G] (h : Equation1037 G) : Equation1051 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2 in 12
  have eq35 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq11 eq19 -- superposition 19,11, 11 into 19, unify on (0).2 in 11 and (0).1.2.1 in 19
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq47 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq37 eq35 -- backward demodulation 35,37
  have eq49 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq37 eq27 -- backward demodulation 27,37
  have eq51 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq47 eq10 -- backward demodulation 10,47
  have eq64 : sK0 ≠ sK0 := superpose eq49 eq51 -- superposition 51,49, 49 into 51, unify on (0).2 in 49 and (0).2 in 51
  subsumption eq64 rfl


@[equational_result]
theorem Equation1037_implies_Equation832 (G : Type*) [Magma G] (h : Equation1037 G) : Equation832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1037_implies_Equation1834 (G : Type*) [Magma G] (h : Equation1037 G) : Equation1834 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2 in 12
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq49 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq37 eq27 -- backward demodulation 27,37
  have eq51 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq37 eq10 -- backward demodulation 10,37
  subsumption eq51 eq49


@[equational_result]
theorem Equation1037_implies_Equation3723 (G : Type*) [Magma G] (h : Equation1037 G) : Equation3723 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq28 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1.2 in 9
  have eq35 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq11 eq19 -- superposition 19,11, 11 into 19, unify on (0).2 in 11 and (0).1.2.1 in 19
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq47 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq37 eq35 -- backward demodulation 35,37
  have eq48 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq37 eq28 -- backward demodulation 28,37
  have eq102 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq47 eq48 -- superposition 48,47, 47 into 48, unify on (0).2 in 47 and (0).1.2.1 in 48
  have eq246 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq102 eq10 -- superposition 10,102, 102 into 10, unify on (0).2 in 102 and (0).2 in 10
  subsumption eq246 rfl


@[equational_result]
theorem Equation1037_implies_Equation1636 (G : Type*) [Magma G] (h : Equation1037 G) : Equation1636 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq26 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2 in 12
  have eq27 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1.2 in 9
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq48 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq37 eq27 -- backward demodulation 27,37
  have eq49 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq37 eq26 -- backward demodulation 26,37
  have eq58 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq49 eq12 -- superposition 12,49, 49 into 12, unify on (0).2 in 49 and (0).1.2 in 12
  have eq74 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) := superpose eq58 eq10 -- backward demodulation 10,58
  subsumption eq74 eq48


@[equational_result]
theorem Equation1037_implies_Equation1233 (G : Type*) [Magma G] (h : Equation1037 G) : Equation1233 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq19 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq26 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2 in 12
  have eq35 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq11 eq19 -- superposition 19,11, 11 into 19, unify on (0).2 in 11 and (0).1.2.1 in 19
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq47 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq37 eq35 -- backward demodulation 35,37
  have eq49 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq37 eq26 -- backward demodulation 26,37
  have eq50 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq37 eq17 -- backward demodulation 17,37
  have eq54 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq49 eq49 -- superposition 49,49, 49 into 49, unify on (0).2 in 49 and (0).1.2 in 49
  have eq63 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := superpose eq54 eq10 -- backward demodulation 10,54
  have eq94 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq47 eq50 -- superposition 50,47, 47 into 50, unify on (0).2 in 47 and (0).1 in 50
  have eq148 : sK0 ≠ sK0 := superpose eq94 eq63 -- superposition 63,94, 94 into 63, unify on (0).2 in 94 and (0).2 in 63
  subsumption eq148 rfl


@[equational_result]
theorem Equation1037_implies_Equation378 (G : Type*) [Magma G] (h : Equation1037 G) : Equation378 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq26 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2 in 12
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq49 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq37 eq26 -- backward demodulation 26,37
  have eq54 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq49 eq49 -- superposition 49,49, 49 into 49, unify on (0).2 in 49 and (0).1.2 in 49
  have eq117 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq54 eq10 -- superposition 10,54, 54 into 10, unify on (0).2 in 54 and (0).2 in 10
  subsumption eq117 rfl


@[equational_result]
theorem Equation1037_implies_Equation1030 (G : Type*) [Magma G] (h : Equation1037 G) : Equation1030 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq19 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2 in 12
  have eq35 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq11 eq19 -- superposition 19,11, 11 into 19, unify on (0).2 in 11 and (0).1.2.1 in 19
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq47 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq37 eq35 -- backward demodulation 35,37
  have eq49 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq37 eq27 -- backward demodulation 27,37
  have eq50 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq37 eq17 -- backward demodulation 17,37
  have eq58 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq49 eq12 -- superposition 12,49, 49 into 12, unify on (0).2 in 49 and (0).1.2 in 12
  have eq74 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := superpose eq58 eq10 -- backward demodulation 10,58
  have eq94 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq47 eq50 -- superposition 50,47, 47 into 50, unify on (0).2 in 47 and (0).1 in 50
  have eq156 : sK0 ≠ sK0 := superpose eq94 eq74 -- superposition 74,94, 94 into 74, unify on (0).2 in 94 and (0).2 in 74
  subsumption eq156 rfl


@[equational_result]
theorem Equation1037_implies_Equation2462 (G : Type*) [Magma G] (h : Equation1037 G) : Equation2462 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2 in 12
  have eq28 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1.2 in 9
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq48 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq37 eq28 -- backward demodulation 28,37
  have eq49 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq37 eq27 -- backward demodulation 27,37
  have eq51 : sK0 ≠ (sK0 ◇ sK0) := superpose eq48 eq10 -- backward demodulation 10,48
  have eq59 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq49 eq12 -- superposition 12,49, 49 into 12, unify on (0).2 in 49 and (0).1.2 in 12
  have eq78 : sK0 ≠ sK0 := superpose eq59 eq51 -- superposition 51,59, 59 into 51, unify on (0).2 in 59 and (0).2 in 51
  subsumption eq78 rfl


@[equational_result]
theorem Equation1037_implies_Equation852 (G : Type*) [Magma G] (h : Equation1037 G) : Equation852 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation1037_implies_Equation841 (G : Type*) [Magma G] (h : Equation1037 G) : Equation841 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq28 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1.2 in 9
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq48 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq37 eq28 -- backward demodulation 28,37
  have eq81 : sK0 ≠ sK0 := superpose eq48 eq10 -- superposition 10,48, 48 into 10, unify on (0).2 in 48 and (0).2 in 10
  subsumption eq81 rfl


@[equational_result]
theorem Equation1037_implies_Equation1231 (G : Type*) [Magma G] (h : Equation1037 G) : Equation1231 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq26 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2 in 12
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq49 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq37 eq26 -- backward demodulation 26,37
  have eq57 : sK0 ≠ sK0 := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2 in 10
  subsumption eq57 rfl


@[equational_result]
theorem Equation1037_implies_Equation1244 (G : Type*) [Magma G] (h : Equation1037 G) : Equation1244 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2 in 12
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq49 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq37 eq27 -- backward demodulation 27,37
  have eq63 : sK0 ≠ sK0 := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2 in 10
  subsumption eq63 rfl


@[equational_result]
theorem Equation1037_implies_Equation1853 (G : Type*) [Magma G] (h : Equation1037 G) : Equation1853 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2 in 12
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq49 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq37 eq27 -- backward demodulation 27,37
  have eq51 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK0)) := superpose eq49 eq10 -- backward demodulation 10,49
  subsumption eq51 eq49


@[equational_result]
theorem Equation1037_implies_Equation426 (G : Type*) [Magma G] (h : Equation1037 G) : Equation426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2 in 12
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq49 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq37 eq27 -- backward demodulation 27,37
  have eq51 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq37 eq10 -- backward demodulation 10,37
  subsumption eq51 eq49


@[equational_result]
theorem Equation1037_implies_Equation3322 (G : Type*) [Magma G] (h : Equation1037 G) : Equation3322 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2 in 12
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq49 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq37 eq27 -- backward demodulation 27,37
  have eq51 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq49 eq10 -- backward demodulation 10,49
  subsumption eq51 rfl


@[equational_result]
theorem Equation1037_implies_Equation1048 (G : Type*) [Magma G] (h : Equation1037 G) : Equation1048 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2 in 12
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq49 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq37 eq27 -- backward demodulation 27,37
  have eq51 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq37 eq10 -- backward demodulation 10,37
  subsumption eq51 eq49


@[equational_result]
theorem Equation1037_implies_Equation427 (G : Type*) [Magma G] (h : Equation1037 G) : Equation427 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2 in 12
  have eq35 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq11 eq19 -- superposition 19,11, 11 into 19, unify on (0).2 in 11 and (0).1.2.1 in 19
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq47 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq37 eq35 -- backward demodulation 35,37
  have eq49 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq37 eq27 -- backward demodulation 27,37
  have eq51 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq47 eq10 -- backward demodulation 10,47
  have eq64 : sK0 ≠ sK0 := superpose eq49 eq51 -- superposition 51,49, 49 into 51, unify on (0).2 in 49 and (0).2 in 51
  subsumption eq64 rfl


@[equational_result]
theorem Equation1037_implies_Equation3463 (G : Type*) [Magma G] (h : Equation1037 G) : Equation3463 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2 in 12
  have eq28 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1.2 in 9
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq48 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq37 eq28 -- backward demodulation 28,37
  have eq49 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq37 eq27 -- backward demodulation 27,37
  have eq51 : sK0 ≠ (sK0 ◇ sK0) := superpose eq48 eq10 -- backward demodulation 10,48
  have eq59 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq49 eq12 -- superposition 12,49, 49 into 12, unify on (0).2 in 49 and (0).1.2 in 12
  have eq78 : sK0 ≠ sK0 := superpose eq59 eq51 -- superposition 51,59, 59 into 51, unify on (0).2 in 59 and (0).2 in 51
  subsumption eq78 rfl


@[equational_result]
theorem Equation1037_implies_Equation428 (G : Type*) [Magma G] (h : Equation1037 G) : Equation428 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2 in 12
  have eq35 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq11 eq19 -- superposition 19,11, 11 into 19, unify on (0).2 in 11 and (0).1.2.1 in 19
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq47 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq37 eq35 -- backward demodulation 35,37
  have eq49 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq37 eq27 -- backward demodulation 27,37
  have eq51 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq47 eq10 -- backward demodulation 10,47
  have eq64 : sK0 ≠ sK0 := superpose eq49 eq51 -- superposition 51,49, 49 into 51, unify on (0).2 in 49 and (0).2 in 51
  subsumption eq64 rfl


@[equational_result]
theorem Equation1037_implies_Equation1235 (G : Type*) [Magma G] (h : Equation1037 G) : Equation1235 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq19 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2 in 12
  have eq35 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq11 eq19 -- superposition 19,11, 11 into 19, unify on (0).2 in 11 and (0).1.2.1 in 19
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq47 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq37 eq35 -- backward demodulation 35,37
  have eq49 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq37 eq27 -- backward demodulation 27,37
  have eq50 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq37 eq17 -- backward demodulation 17,37
  have eq51 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X2) = (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) := superpose eq9 eq49 -- superposition 49,9, 9 into 49, unify on (0).2 in 9 and (0).1.2 in 49
  have eq60 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq49 eq12 -- superposition 12,49, 49 into 12, unify on (0).2 in 49 and (0).1.2 in 12
  have eq71 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq60 eq51 -- backward demodulation 51,60
  have eq74 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := superpose eq71 eq10 -- backward demodulation 10,71
  have eq93 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq47 eq50 -- superposition 50,47, 47 into 50, unify on (0).2 in 47 and (0).1 in 50
  have eq154 : sK0 ≠ sK0 := superpose eq93 eq74 -- superposition 74,93, 93 into 74, unify on (0).2 in 93 and (0).2 in 74
  subsumption eq154 rfl


@[equational_result]
theorem Equation1037_implies_Equation1237 (G : Type*) [Magma G] (h : Equation1037 G) : Equation1237 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq19 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq35 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq11 eq19 -- superposition 19,11, 11 into 19, unify on (0).2 in 11 and (0).1.2.1 in 19
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq47 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq37 eq35 -- backward demodulation 35,37
  have eq50 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq37 eq17 -- backward demodulation 17,37
  have eq101 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq47 eq50 -- superposition 50,47, 47 into 50, unify on (0).2 in 47 and (0).1 in 50
  have eq177 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = X0 := superpose eq101 eq50 -- superposition 50,101, 101 into 50, unify on (0).2 in 101 and (0).1 in 50
  have eq341 : sK0 ≠ sK0 := superpose eq177 eq10 -- superposition 10,177, 177 into 10, unify on (0).2 in 177 and (0).2 in 10
  subsumption eq341 rfl


@[equational_result]
theorem Equation2042_implies_Equation2893 (G : Type*) [Magma G] (h : Equation2042 G) : Equation2893 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq26 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ X1) = ((((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) ◇ X2) ◇ (X0 ◇ X0)) := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).1.1 in 12
  have eq36 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq9 eq26 -- forward demodulation 26,9
  have eq40 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq36 eq12 -- superposition 12,36, 36 into 12, unify on (0).2 in 36 and (0).2.1.1 in 12
  have eq50 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ X0) := superpose eq40 eq40 -- superposition 40,40, 40 into 40, unify on (0).2 in 40 and (0).1 in 40
  have eq55 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq40 eq11 -- superposition 11,40, 40 into 11, unify on (0).2 in 40 and (0).2.2 in 11
  have eq56 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq40 eq9 -- superposition 9,40, 40 into 9, unify on (0).2 in 40 and (0).1.1 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := superpose eq40 eq12 -- superposition 12,40, 40 into 12, unify on (0).2 in 40 and (0).2.1 in 12
  have eq107 (X0 X1 X3 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ X3) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq50 -- superposition 50,9, 9 into 50, unify on (0).2 in 9 and (0).1.1 in 50
  have eq114 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq50 eq50 -- superposition 50,50, 50 into 50, unify on (0).2 in 50 and (0).1.1 in 50
  have eq161 (X0 X1 X3 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ X3) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq11 eq107 -- forward demodulation 107,11
  have eq162 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose eq161 eq57 -- backward demodulation 57,161
  have eq167 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = X0 := superpose eq56 eq114 -- forward demodulation 114,56
  have eq206 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq9 eq55 -- superposition 55,9, 9 into 55, unify on (0).2 in 9 and (0).2.2.1 in 55
  have eq215 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq50 eq55 -- superposition 55,50, 50 into 55, unify on (0).2 in 50 and (0).2.2.1 in 55
  have eq236 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq9 eq206 -- forward demodulation 206,9
  have eq238 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X3) ◇ X0) := superpose eq236 eq12 -- backward demodulation 12,236
  have eq241 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq56 eq215 -- forward demodulation 215,56
  have eq242 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ X1) = ((((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2) ◇ (X0 ◇ X0)) := superpose eq241 eq32 -- backward demodulation 32,241
  have eq246 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X1) := superpose eq167 eq242 -- forward demodulation 242,167
  have eq247 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq9 eq246 -- forward demodulation 246,9
  have eq271 (X0 X1 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq238 -- superposition 238,9, 9 into 238, unify on (0).2 in 9 and (0).2.1 in 238
  have eq339 (X0 X1 X3 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3) := superpose eq11 eq271 -- forward demodulation 271,11
  have eq340 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq236 eq339 -- forward demodulation 339,236
  have eq341 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK2) ◇ sK3) := superpose eq340 eq10 -- backward demodulation 10,340
  have eq342 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK3) := superpose eq162 eq341 -- forward demodulation 341,162
  subsumption eq342 eq247


@[equational_result]
theorem Equation618_implies_Equation413 (G : Type*) [Magma G] (h : Equation618 G) : Equation413 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation618_implies_Equation412 (G : Type*) [Magma G] (h : Equation618 G) : Equation412 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq16 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq24 : sK0 ≠ sK0 := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).2 in 13
  subsumption eq24 rfl


@[equational_result]
theorem Equation618_implies_Equation414 (G : Type*) [Magma G] (h : Equation618 G) : Equation414 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation618_implies_Equation415 (G : Type*) [Magma G] (h : Equation618 G) : Equation415 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation618_implies_Equation4380 (G : Type*) [Magma G] (h : Equation618 G) : Equation4380 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.1 in 8
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.2 in 10
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2 in 10
  have eq18 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq12 eq9 -- backward demodulation 9,12
  have eq20 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq18 -- backward demodulation 18,14
  subsumption eq20 eq14


@[equational_result]
theorem Equation3889_implies_Equation3894 (G : Type*) [Magma G] (h : Equation3889 G) : Equation3894 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq17 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq18 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq18 eq18 -- superposition 18,18, 18 into 18, unify on (0).2 in 18 and (0).2 in 18
  have eq54 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq17 -- superposition 17,27, 27 into 17, unify on (0).2 in 27 and (0).2 in 17
  subsumption eq54 eq27


@[equational_result]
theorem Equation3889_implies_Equation3896 (G : Type*) [Magma G] (h : Equation3889 G) : Equation3896 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK3) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq17 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq18 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq18 eq18 -- superposition 18,18, 18 into 18, unify on (0).2 in 18 and (0).2 in 18
  have eq54 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq17 -- superposition 17,27, 27 into 17, unify on (0).2 in 27 and (0).2 in 17
  subsumption eq54 eq27


@[equational_result]
theorem Equation3899_implies_Equation4067 (G : Type*) [Magma G] (h : Equation3899 G) : Equation4067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq29 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq29 eq15


@[equational_result]
theorem Equation3899_implies_Equation4341 (G : Type*) [Magma G] (h : Equation3899 G) : Equation4341 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq22 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq93 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).2.2 in 10
  subsumption eq93 rfl


@[equational_result]
theorem Equation3899_implies_Equation3883 (G : Type*) [Magma G] (h : Equation3899 G) : Equation3883 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq50 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq50 eq23


@[equational_result]
theorem Equation3899_implies_Equation3870 (G : Type*) [Magma G] (h : Equation3899 G) : Equation3870 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq22 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq93 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK0 ◇ (X0 ◇ X0)) ◇ sK0) := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).2.1.2 in 10
  have eq914 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq9 eq93 -- superposition 93,9, 9 into 93, unify on (0).2 in 9 and (0).2 in 93
  subsumption eq914 rfl


@[equational_result]
theorem Equation3899_implies_Equation3911 (G : Type*) [Magma G] (h : Equation3899 G) : Equation3911 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK2) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq50 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq50 eq23


@[equational_result]
theorem Equation3899_implies_Equation3880 (G : Type*) [Magma G] (h : Equation3899 G) : Equation3880 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq50 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq50 eq23


@[equational_result]
theorem Equation3899_implies_Equation3685 (G : Type*) [Magma G] (h : Equation3899 G) : Equation3685 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq22 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq32 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq32 eq22


@[equational_result]
theorem Equation3899_implies_Equation3690 (G : Type*) [Magma G] (h : Equation3899 G) : Equation3690 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq22 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq29 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq29 eq22


@[equational_result]
theorem Equation3899_implies_Equation3684 (G : Type*) [Magma G] (h : Equation3899 G) : Equation3684 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq22 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq29 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq29 eq22


@[equational_result]
theorem Equation3899_implies_Equation4622 (G : Type*) [Magma G] (h : Equation3899 G) : Equation4622 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq29 (X0 : G) : (X0 ◇ X0) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq29 eq15


@[equational_result]
theorem Equation3899_implies_Equation3906 (G : Type*) [Magma G] (h : Equation3899 G) : Equation3906 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X2) = ((X3 ◇ (X4 ◇ X0)) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq22 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq48 (X1 X2 X3 X4 : G) : (X2 ◇ X2) = ((X3 ◇ (X4 ◇ X1)) ◇ X4) := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1 in 11
  have eq93 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ (X0 ◇ X0)) ◇ sK1) := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).2.1.2 in 10
  have eq625 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ X4) = ((X5 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X2)) ◇ X0) := superpose eq48 eq48 -- superposition 48,48, 48 into 48, unify on (0).2 in 48 and (0).2.1.2 in 48
  have eq896 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2)) ◇ sK1) := superpose eq9 eq93 -- superposition 93,9, 9 into 93, unify on (0).2 in 9 and (0).2.1.2 in 93
  subsumption eq896 eq625


@[equational_result]
theorem Equation3899_implies_Equation3662 (G : Type*) [Magma G] (h : Equation3899 G) : Equation3662 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq22 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq29 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq29 eq22


@[equational_result]
theorem Equation3899_implies_Equation3660 (G : Type*) [Magma G] (h : Equation3899 G) : Equation3660 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq22 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq29 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq29 eq22


@[equational_result]
theorem Equation3899_implies_Equation3665 (G : Type*) [Magma G] (h : Equation3899 G) : Equation3665 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq26 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ X1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq26 eq15


@[equational_result]
theorem Equation3899_implies_Equation3864 (G : Type*) [Magma G] (h : Equation3899 G) : Equation3864 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq50 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq50 eq23


@[equational_result]
theorem Equation769_implies_Equation1623 (G : Type*) [Magma G] (h : Equation769 G) : Equation1623 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ (sK4 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ (X3 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation447_implies_Equation3728 (G : Type*) [Magma G] (h : Equation447 G) : Equation3728 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq26 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK1)) := superpose eq18 eq10 -- backward demodulation 10,18
  subsumption eq26 eq18


@[equational_result]
theorem Equation447_implies_Equation1836 (G : Type*) [Magma G] (h : Equation447 G) : Equation1836 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq26 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq18 eq10 -- backward demodulation 10,18
  subsumption eq26 eq18


@[equational_result]
theorem Equation447_implies_Equation646 (G : Type*) [Magma G] (h : Equation447 G) : Equation646 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq26 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := superpose eq18 eq10 -- backward demodulation 10,18
  subsumption eq26 eq18


@[equational_result]
theorem Equation447_implies_Equation460 (G : Type*) [Magma G] (h : Equation447 G) : Equation460 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq26 : sK0 ≠ (sK0 ◇ sK1) := superpose eq18 eq10 -- backward demodulation 10,18
  subsumption eq26 eq18


@[equational_result]
theorem Equation447_implies_Equation2250 (G : Type*) [Magma G] (h : Equation447 G) : Equation2250 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq26 : sK0 ≠ (sK0 ◇ sK1) := superpose eq18 eq10 -- backward demodulation 10,18
  subsumption eq26 eq18


@[equational_result]
theorem Equation447_implies_Equation4511 (G : Type*) [Magma G] (h : Equation447 G) : Equation4511 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq26 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK1) := superpose eq18 eq10 -- backward demodulation 10,18
  have eq27 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq18 eq26 -- forward demodulation 26,18
  subsumption eq27 eq18


@[equational_result]
theorem Equation447_implies_Equation645 (G : Type*) [Magma G] (h : Equation447 G) : Equation645 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq26 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := superpose eq18 eq10 -- backward demodulation 10,18
  subsumption eq26 eq18


@[equational_result]
theorem Equation447_implies_Equation256 (G : Type*) [Magma G] (h : Equation447 G) : Equation256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq26 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq18 eq10 -- backward demodulation 10,18
  have eq27 : sK0 ≠ (sK0 ◇ sK1) := superpose eq18 eq26 -- forward demodulation 26,18
  subsumption eq27 eq18


@[equational_result]
theorem Equation447_implies_Equation2057 (G : Type*) [Magma G] (h : Equation447 G) : Equation2057 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq26 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) := superpose eq18 eq10 -- backward demodulation 10,18
  have eq27 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq18 eq26 -- forward demodulation 26,18
  have eq28 : sK0 ≠ (sK0 ◇ sK2) := superpose eq18 eq27 -- forward demodulation 27,18
  subsumption eq28 eq18


@[equational_result]
theorem Equation447_implies_Equation432 (G : Type*) [Magma G] (h : Equation447 G) : Equation432 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq26 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq18 eq10 -- backward demodulation 10,18
  subsumption eq26 eq18


@[equational_result]
theorem Equation447_implies_Equation3932 (G : Type*) [Magma G] (h : Equation447 G) : Equation3932 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq26 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK2) := superpose eq18 eq10 -- backward demodulation 10,18
  have eq27 : sK0 ≠ (sK0 ◇ sK1) := superpose eq18 eq26 -- forward demodulation 26,18
  subsumption eq27 eq18


@[equational_result]
theorem Equation54_implies_Equation2877 (G : Type*) [Magma G] (h : Equation54 G) : Equation2877 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK2) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation54_implies_Equation102 (G : Type*) [Magma G] (h : Equation54 G) : Equation102 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation54_implies_Equation3738 (G : Type*) [Magma G] (h : Equation54 G) : Equation3738 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK3)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation54_implies_Equation1856 (G : Type*) [Magma G] (h : Equation54 G) : Equation1856 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK3)) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq16 : sK0 ≠ (sK0 ◇ sK2) := superpose eq12 eq13 -- backward demodulation 13,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation54_implies_Equation1224 (G : Type*) [Magma G] (h : Equation54 G) : Equation1224 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation54_implies_Equation3924 (G : Type*) [Magma G] (h : Equation54 G) : Equation3924 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq13 -- backward demodulation 13,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation449_implies_Equation2872 (G : Type*) [Magma G] (h : Equation449 G) : Equation2872 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ (X4 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq18 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation449_implies_Equation2869 (G : Type*) [Magma G] (h : Equation449 G) : Equation2869 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ (X4 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq18 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation449_implies_Equation4477 (G : Type*) [Magma G] (h : Equation449 G) : Equation4477 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ (X4 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq18 : sK0 ≠ (sK0 ◇ sK2) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation449_implies_Equation655 (G : Type*) [Magma G] (h : Equation449 G) : Equation655 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ (X4 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq16 eq14


@[equational_result]
theorem Equation449_implies_Equation631 (G : Type*) [Magma G] (h : Equation449 G) : Equation631 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ (X4 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq16 eq14


@[equational_result]
theorem Equation238_implies_Equation1055 (G : Type*) [Magma G] (h : Equation238 G) : Equation1055 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq11 : sK0 ≠ (sK0 ◇ sK0) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq18 : sK0 ≠ sK0 := superpose eq14 eq11 -- superposition 11,14, 14 into 11, unify on (0).2 in 14 and (0).2 in 11
  subsumption eq18 rfl


@[equational_result]
theorem Equation238_implies_Equation1847 (G : Type*) [Magma G] (h : Equation238 G) : Equation1847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq17 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq9


@[equational_result]
theorem Equation238_implies_Equation3897 (G : Type*) [Magma G] (h : Equation238 G) : Equation3897 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq11 : sK0 ≠ (sK0 ◇ sK0) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq18 : sK0 ≠ sK0 := superpose eq14 eq11 -- superposition 11,14, 14 into 11, unify on (0).2 in 14 and (0).2 in 11
  subsumption eq18 rfl


@[equational_result]
theorem Equation238_implies_Equation2327 (G : Type*) [Magma G] (h : Equation238 G) : Equation2327 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq17 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq9


@[equational_result]
theorem Equation238_implies_Equation1921 (G : Type*) [Magma G] (h : Equation238 G) : Equation1921 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq17 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq9


@[equational_result]
theorem Equation431_implies_Equation461 (G : Type*) [Magma G] (h : Equation431 G) : Equation461 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X3 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation431_implies_Equation2073 (G : Type*) [Magma G] (h : Equation431 G) : Equation2073 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK0 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X3 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK3)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq14 eq17 -- forward demodulation 17,14
  have eq19 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq18 -- forward demodulation 18,14
  subsumption eq19 eq14


@[equational_result]
theorem Equation460_implies_Equation839 (G : Type*) [Magma G] (h : Equation460 G) : Equation839 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq16 eq13


@[equational_result]
theorem Equation460_implies_Equation2892 (G : Type*) [Magma G] (h : Equation460 G) : Equation2892 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq13 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq17 : sK0 ≠ (sK0 ◇ sK2) := superpose eq13 eq16 -- forward demodulation 16,13
  subsumption eq17 eq13


@[equational_result]
theorem Equation460_implies_Equation4384 (G : Type*) [Magma G] (h : Equation460 G) : Equation4384 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq13 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq17 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq13 eq16 -- forward demodulation 16,13
  subsumption eq17 eq13


@[equational_result]
theorem Equation460_implies_Equation4401 (G : Type*) [Magma G] (h : Equation460 G) : Equation4401 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq13 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq17 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq16 -- forward demodulation 16,13
  subsumption eq17 eq13


@[equational_result]
theorem Equation460_implies_Equation3875 (G : Type*) [Magma G] (h : Equation460 G) : Equation3875 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq13 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq17 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq16 -- forward demodulation 16,13
  subsumption eq17 eq13


@[equational_result]
theorem Equation460_implies_Equation428 (G : Type*) [Magma G] (h : Equation460 G) : Equation428 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq13 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq16 eq13


@[equational_result]
theorem Equation460_implies_Equation455 (G : Type*) [Magma G] (h : Equation460 G) : Equation455 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq13 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq16 eq13


@[equational_result]
theorem Equation460_implies_Equation1068 (G : Type*) [Magma G] (h : Equation460 G) : Equation1068 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq16 eq13


@[equational_result]
theorem Equation460_implies_Equation204 (G : Type*) [Magma G] (h : Equation460 G) : Equation204 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq16 eq13


@[equational_result]
theorem Equation460_implies_Equation3865 (G : Type*) [Magma G] (h : Equation460 G) : Equation3865 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq17 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq16 -- forward demodulation 16,13
  subsumption eq17 eq13


@[equational_result]
theorem Equation3600_implies_Equation4128 (G : Type*) [Magma G] (h : Equation3600 G) : Equation4128 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X1 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq17 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X2 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq22 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq17 eq10 -- backward demodulation 10,17
  subsumption eq22 eq17


@[equational_result]
theorem Equation3600_implies_Equation4006 (G : Type*) [Magma G] (h : Equation3600 G) : Equation4006 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X1 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X2 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq26 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).2 in 15
  subsumption eq26 rfl


@[equational_result]
theorem Equation3600_implies_Equation3877 (G : Type*) [Magma G] (h : Equation3600 G) : Equation3877 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X1 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X2 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq26 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).2 in 15
  subsumption eq26 rfl


@[equational_result]
theorem Equation3600_implies_Equation343 (G : Type*) [Magma G] (h : Equation3600 G) : Equation343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X1 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq21 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation3600_implies_Equation4435 (G : Type*) [Magma G] (h : Equation3600 G) : Equation4435 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X1 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK1 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X2 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq26 : (sK1 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).2 in 15
  subsumption eq26 rfl


@[equational_result]
theorem Equation3600_implies_Equation385 (G : Type*) [Magma G] (h : Equation3600 G) : Equation385 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X1 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq17 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X2 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq25 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq25 rfl


@[equational_result]
theorem Equation3600_implies_Equation4483 (G : Type*) [Magma G] (h : Equation3600 G) : Equation4483 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X1 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK1 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X2 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq28 : (sK1 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).2 in 15
  subsumption eq28 rfl


@[equational_result]
theorem Equation3600_implies_Equation4406 (G : Type*) [Magma G] (h : Equation3600 G) : Equation4406 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X1 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : ((sK1 ◇ sK0) ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : ((sK1 ◇ sK0) ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X2 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq26 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).1 in 15
  subsumption eq26 rfl


@[equational_result]
theorem Equation3600_implies_Equation4546 (G : Type*) [Magma G] (h : Equation3600 G) : Equation4546 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X1 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK1 ◇ sK2) ≠ ((sK2 ◇ sK1) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X2) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq26 : (sK1 ◇ sK2) ≠ (sK1 ◇ sK2) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).2 in 15
  subsumption eq26 rfl


@[equational_result]
theorem Equation1235_implies_Equation3457 (G : Type*) [Magma G] (h : Equation1235 G) : Equation3457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.1 in 12
  have eq17 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq18 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq36 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq55 : sK0 ≠ sK0 := superpose eq36 eq18 -- superposition 18,36, 36 into 18, unify on (0).2 in 36 and (0).2 in 18
  subsumption eq55 rfl


@[equational_result]
theorem Equation1235_implies_Equation824 (G : Type*) [Magma G] (h : Equation1235 G) : Equation824 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq28 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X1))) = X0 := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).1.2.1.1 in 9
  have eq105 : sK0 ≠ sK0 := superpose eq51 eq10 -- superposition 10,51, 51 into 10, unify on (0).2 in 51 and (0).2 in 10
  subsumption eq105 rfl


@[equational_result]
theorem Equation1235_implies_Equation822 (G : Type*) [Magma G] (h : Equation1235 G) : Equation822 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.1 in 12
  have eq17 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq18 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq21 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.2.1.1 in 9
  have eq91 : sK0 ≠ sK0 := superpose eq21 eq18 -- superposition 18,21, 21 into 18, unify on (0).2 in 21 and (0).2 in 18
  subsumption eq91 rfl


@[equational_result]
theorem Equation1235_implies_Equation102 (G : Type*) [Magma G] (h : Equation1235 G) : Equation102 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation636_implies_Equation3736 (G : Type*) [Magma G] (h : Equation636 G) : Equation3736 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq34 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2 in 9
  have eq62 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK1) := superpose eq34 eq10 -- backward demodulation 10,34
  have eq63 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq34 eq62 -- forward demodulation 62,34
  subsumption eq63 rfl


@[equational_result]
theorem Equation636_implies_Equation855 (G : Type*) [Magma G] (h : Equation636 G) : Equation855 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK3))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq34 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2 in 9
  have eq62 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq34 eq10 -- backward demodulation 10,34
  subsumption eq62 eq34


@[equational_result]
theorem Equation636_implies_Equation658 (G : Type*) [Magma G] (h : Equation636 G) : Equation658 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK2) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq34 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2 in 9
  have eq62 : sK0 ≠ (sK0 ◇ sK1) := superpose eq34 eq10 -- backward demodulation 10,34
  subsumption eq62 eq34


@[equational_result]
theorem Equation636_implies_Equation653 (G : Type*) [Magma G] (h : Equation636 G) : Equation653 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq34 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2 in 9
  have eq62 : sK0 ≠ (sK0 ◇ sK1) := superpose eq34 eq10 -- backward demodulation 10,34
  subsumption eq62 eq34


@[equational_result]
theorem Equation2536_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2536 G) : Equation2644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq15 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1.1.2 in 10
  have eq20 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq8 eq15 -- forward demodulation 15,8
  have eq54 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).1.1 in 10
  have eq67 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq54 eq20 -- superposition 20,54, 54 into 20, unify on (0).2 in 54 and (0).2.1.2 in 20
  have eq77 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq67 eq9 -- backward demodulation 9,67
  subsumption eq77 eq54


@[equational_result]
theorem Equation2536_implies_Equation3145 (G : Type*) [Magma G] (h : Equation2536 G) : Equation3145 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK0) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq70 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq55 eq11 -- superposition 11,55, 55 into 11, unify on (0).2 in 55 and (0).1.1.1.2 in 11
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.1.2.1 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq340 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.1.2 in 9
  have eq363 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq68 eq340 -- forward demodulation 340,68
  have eq373 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq363 eq70 -- backward demodulation 70,363
  have eq391 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK0) := superpose eq363 eq10 -- backward demodulation 10,363
  subsumption eq391 eq373


@[equational_result]
theorem Equation2536_implies_Equation3058 (G : Type*) [Magma G] (h : Equation2536 G) : Equation3058 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.1.2.1 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq340 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.1.2 in 9
  have eq363 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq68 eq340 -- forward demodulation 340,68
  have eq391 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq363 eq10 -- backward demodulation 10,363
  subsumption eq391 eq363


@[equational_result]
theorem Equation2536_implies_Equation3115 (G : Type*) [Magma G] (h : Equation2536 G) : Equation3115 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq70 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq55 eq11 -- superposition 11,55, 55 into 11, unify on (0).2 in 55 and (0).1.1.1.2 in 11
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.1.2.1 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq340 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.1.2 in 9
  have eq363 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq68 eq340 -- forward demodulation 340,68
  have eq373 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq363 eq70 -- backward demodulation 70,363
  have eq394 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq373 eq10 -- backward demodulation 10,373
  subsumption eq394 eq363


@[equational_result]
theorem Equation2536_implies_Equation2355 (G : Type*) [Magma G] (h : Equation2536 G) : Equation2355 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1.2 in 11
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq19 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X1 ◇ X3)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq22 (X1 X3 : G) : (X1 ◇ X3) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq23 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK0) := superpose eq22 eq10 -- backward demodulation 10,22
  have eq56 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq111 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq56 eq21 -- superposition 21,56, 56 into 21, unify on (0).2 in 56 and (0).2.1.2 in 21
  have eq294 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq111 eq15 -- superposition 15,111, 111 into 15, unify on (0).2 in 111 and (0).1 in 15
  have eq318 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq294 -- forward demodulation 294,12
  have eq434 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq318 eq9 -- superposition 9,318, 318 into 9, unify on (0).2 in 318 and (0).1.1.2 in 9
  have eq461 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq111 eq434 -- forward demodulation 434,111
  have eq467 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq461 eq318 -- backward demodulation 318,461
  have eq503 : sK0 ≠ ((sK2 ◇ sK2) ◇ sK0) := superpose eq467 eq23 -- backward demodulation 23,467
  subsumption eq503 eq461


@[equational_result]
theorem Equation2536_implies_Equation2672 (G : Type*) [Magma G] (h : Equation2536 G) : Equation2672 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq68 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).1 in 21
  have eq74 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq224 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq74 eq68 -- superposition 68,74, 74 into 68, unify on (0).2 in 74 and (0).1.1.1 in 68
  have eq246 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq224 -- forward demodulation 224,12
  have eq355 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq246 eq9 -- superposition 9,246, 246 into 9, unify on (0).2 in 246 and (0).1.1.2 in 9
  have eq364 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq74 eq355 -- forward demodulation 355,74
  have eq370 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq364 eq246 -- backward demodulation 246,364
  have eq408 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq370 eq10 -- backward demodulation 10,370
  subsumption eq408 eq364


@[equational_result]
theorem Equation2536_implies_Equation2318 (G : Type*) [Magma G] (h : Equation2536 G) : Equation2318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.1.2.1 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq340 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.1.2 in 9
  have eq363 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq68 eq340 -- forward demodulation 340,68
  have eq366 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq363 eq144 -- backward demodulation 144,363
  have eq394 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK0) := superpose eq366 eq10 -- backward demodulation 10,366
  have eq395 : sK0 ≠ ((sK2 ◇ sK2) ◇ sK0) := superpose eq366 eq394 -- forward demodulation 394,366
  subsumption eq395 eq363


@[equational_result]
theorem Equation2536_implies_Equation4165 (G : Type*) [Magma G] (h : Equation2536 G) : Equation4165 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.1.2.1 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq340 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.1.2 in 9
  have eq363 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq68 eq340 -- forward demodulation 340,68
  have eq391 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq363 eq10 -- backward demodulation 10,363
  subsumption eq391 rfl


@[equational_result]
theorem Equation2536_implies_Equation2812 (G : Type*) [Magma G] (h : Equation2536 G) : Equation2812 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK2 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq68 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).1 in 21
  have eq74 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq224 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq74 eq68 -- superposition 68,74, 74 into 68, unify on (0).2 in 74 and (0).1.1.1 in 68
  have eq246 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq224 -- forward demodulation 224,12
  have eq355 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq246 eq9 -- superposition 9,246, 246 into 9, unify on (0).2 in 246 and (0).1.1.2 in 9
  have eq364 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq74 eq355 -- forward demodulation 355,74
  have eq370 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq364 eq246 -- backward demodulation 246,364
  have eq408 : sK0 ≠ ((sK2 ◇ sK2) ◇ sK0) := superpose eq370 eq10 -- backward demodulation 10,370
  subsumption eq408 eq364


