import equational_theories.Superposition
import equational_theories.Equations.All
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation651_implies_Equation54 (G : Type*) [Magma G] (h : Equation651 G) : Equation54 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation654_implies_Equation438 (G : Type*) [Magma G] (h : Equation654 G) : Equation438 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq21 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X1)) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq28 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X0)) = X3 := superpose eq21 eq13 -- backward demodulation 13,21
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq21 eq9 -- backward demodulation 9,21
  have eq30 : sK0 ≠ (sK0 ◇ sK1) := superpose eq28 eq10 -- backward demodulation 10,28
  have eq36 : sK0 ≠ sK0 := superpose eq29 eq30 -- superposition 30,29, 29 into 30, unify on (0).2 in 29 and (0).2 in 30
  subsumption eq36 rfl


@[equational_result]
theorem Equation655_implies_Equation658 (G : Type*) [Magma G] (h : Equation655 G) : Equation658 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK2) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq31 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X3))) = X2 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2.1 in 12
  have eq35 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq46 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X0 ◇ X0) ◇ X3))) = X2 := superpose eq35 eq31 -- backward demodulation 31,35
  have eq102 : sK0 ≠ sK0 := superpose eq46 eq10 -- superposition 10,46, 46 into 10, unify on (0).2 in 46 and (0).2 in 10
  subsumption eq102 rfl


@[equational_result]
theorem Equation66_implies_Equation170 (G : Type*) [Magma G] (h : Equation66 G) : Equation170 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.2 in 9
  have eq15 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq18 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = ((X1 ◇ X1) ◇ X0) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2.1.1 in 16
  have eq24 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose eq18 eq15 -- backward demodulation 15,18
  have eq26 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq11 eq24 -- superposition 24,11, 11 into 24, unify on (0).2 in 11 and (0).1.1.1 in 24
  have eq40 : sK0 ≠ sK0 := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq40 rfl


@[equational_result]
theorem Equation661_implies_Equation848 (G : Type*) [Magma G] (h : Equation661 G) : Equation848 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X4))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation661_implies_Equation860 (G : Type*) [Magma G] (h : Equation661 G) : Equation860 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X4))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation66_implies_Equation281 (G : Type*) [Magma G] (h : Equation66 G) : Equation281 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.2 in 9
  have eq15 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq18 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2.1.1 in 16
  have eq24 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose eq18 eq15 -- backward demodulation 15,18
  have eq31 : sK0 ≠ sK0 := superpose eq24 eq10 -- superposition 10,24, 24 into 10, unify on (0).2 in 24 and (0).2 in 10
  subsumption eq31 rfl


@[equational_result]
theorem Equation666_implies_Equation1598 (G : Type*) [Magma G] (h : Equation666 G) : Equation1598 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = (X1 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq22 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = (X1 ◇ X0) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq23 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = (X1 ◇ X0) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq42 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq23 eq23 -- superposition 23,23, 23 into 23, unify on (0).2 in 23 and (0).1 in 23
  have eq45 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq23 eq13 -- superposition 13,23, 23 into 13, unify on (0).2 in 23 and (0).2.2 in 13
  have eq75 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) := superpose eq42 eq10 -- superposition 10,42, 42 into 10, unify on (0).2 in 42 and (0).2 in 10
  have eq103 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq45 eq45 -- superposition 45,45, 45 into 45, unify on (0).2 in 45 and (0).1.2.1 in 45
  have eq147 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) := superpose eq45 eq103 -- forward demodulation 103,45
  have eq148 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = X1 := superpose eq9 eq147 -- forward demodulation 147,9
  have eq160 (X0 X1 : G) : sK0 ≠ (X1 ◇ (sK2 ◇ (X0 ◇ sK0))) := superpose eq42 eq75 -- superposition 75,42, 42 into 75, unify on (0).2 in 42 and (0).2.2.2 in 75
  subsumption eq160 eq148


@[equational_result]
theorem Equation666_implies_Equation774 (G : Type*) [Magma G] (h : Equation666 G) : Equation774 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK2 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = (X1 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq22 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = (X1 ◇ X0) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq23 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = (X1 ◇ X0) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq45 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq23 eq13 -- superposition 13,23, 23 into 13, unify on (0).2 in 23 and (0).2.2 in 13
  have eq54 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := superpose eq45 eq10 -- backward demodulation 10,45
  subsumption eq54 eq9


@[equational_result]
theorem Equation668_implies_Equation496 (G : Type*) [Magma G] (h : Equation668 G) : Equation496 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK1)))) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq16 : sK0 ≠ (sK1 ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq18 (X1 X3 : G) : X1 = X3 := superpose eq12 eq17 -- superposition 17,12, 12 into 17, unify on (0).2 in 12 and (0).1 in 17
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq16 -- superposition 16,17, 17 into 16, unify on (0).2 in 17 and (0).2 in 16
  subsumption eq21 eq18


@[equational_result]
theorem Equation671_implies_Equation673 (G : Type*) [Magma G] (h : Equation671 G) : Equation673 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq16 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation672_implies_Equation801 (G : Type*) [Magma G] (h : Equation672 G) : Equation801 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK3 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq61 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).1.2 in 11
  have eq62 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (X0 ◇ sK0))) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2.2 in 10
  subsumption eq62 eq61


@[equational_result]
theorem Equation673_implies_Equation1294 (G : Type*) [Magma G] (h : Equation673 G) : Equation1294 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK1) ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq16 eq13 -- backward demodulation 13,16
  have eq23 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq21 eq11 -- backward demodulation 11,21
  have eq27 (X2 X3 : G) : X2 = X3 := superpose eq23 eq23 -- superposition 23,23, 23 into 23, unify on (0).2 in 23 and (0).1 in 23
  have eq29 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ sK3)) := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2.2.1 in 10
  subsumption eq29 eq27


@[equational_result]
theorem Equation67_implies_Equation3144 (G : Type*) [Magma G] (h : Equation67 G) : Equation3144 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK0) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq14 (X1 X2 : G) : X1 = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1 in 13
  have eq18 (X0 : G) : sK0 ≠ (((X0 ◇ sK0) ◇ sK1) ◇ sK2) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1.1 in 10
  subsumption eq18 eq14


@[equational_result]
theorem Equation673_implies_Equation2297 (G : Type*) [Magma G] (h : Equation673 G) : Equation2297 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq16 eq13 -- backward demodulation 13,16
  have eq23 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq21 eq11 -- backward demodulation 11,21
  have eq27 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq21 eq10 -- backward demodulation 10,21
  subsumption eq27 eq23


@[equational_result]
theorem Equation674_implies_Equation668 (G : Type*) [Magma G] (h : Equation674 G) : Equation668 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation678_implies_Equation1696 (G : Type*) [Magma G] (h : Equation678 G) : Equation1696 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq18 (X0 X1 : G) : X0 = X1 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1 in 12
  have eq19 : sK0 ≠ (sK1 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq19 eq18


@[equational_result]
theorem Equation681_implies_Equation705 (G : Type*) [Magma G] (h : Equation681 G) : Equation705 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq14 eq11


@[equational_result]
theorem Equation682_implies_Equation39 (G : Type*) [Magma G] (h : Equation682 G) : Equation39 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq52 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq52 eq15


@[equational_result]
theorem Equation682_implies_Equation869 (G : Type*) [Magma G] (h : Equation682 G) : Equation869 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq60 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.2 in 11
  have eq65 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK0 ◇ sK0))) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq65 eq60


@[equational_result]
theorem Equation683_implies_Equation2941 (G : Type*) [Magma G] (h : Equation683 G) : Equation2941 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq23 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK2) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq23 eq16


@[equational_result]
theorem Equation687_implies_Equation1297 (G : Type*) [Magma G] (h : Equation687 G) : Equation1297 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK2) ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X1 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X1))) ◇ (X1 ◇ X2)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq15 (X1 X2 : G) : ((X2 ◇ X2) ◇ (X1 ◇ X2)) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq35 (X0 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ X0)) = X0 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).1.1.1 in 13
  have eq39 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = (((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) ◇ X1) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).1.2 in 15
  have eq42 (X0 X3 : G) : (X3 ◇ X0) = (((X3 ◇ X0) ◇ (X3 ◇ X0)) ◇ X3) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2 in 15
  have eq52 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = (((X2 ◇ X1) ◇ X0) ◇ X1) := superpose eq14 eq39 -- forward demodulation 39,14
  have eq53 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ sK0))) := superpose eq52 eq10 -- backward demodulation 10,52
  have eq54 (X0 X3 : G) : (X0 ◇ X3) = (X3 ◇ X0) := superpose eq35 eq42 -- forward demodulation 42,35
  have eq56 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) = X0 := superpose eq54 eq13 -- backward demodulation 13,54
  have eq59 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := superpose eq54 eq53 -- backward demodulation 53,54
  have eq88 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := superpose eq9 eq56 -- superposition 56,9, 9 into 56, unify on (0).2 in 9 and (0).1.1 in 56
  have eq107 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq88 eq9 -- backward demodulation 9,88
  have eq108 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X3))) = X0 := superpose eq88 eq11 -- backward demodulation 11,88
  have eq130 : sK0 ≠ (sK1 ◇ sK0) := superpose eq108 eq59 -- backward demodulation 59,108
  have eq156 (X0 X1 : G) : X0 = X1 := superpose eq15 eq107 -- superposition 107,15, 15 into 107, unify on (0).2 in 15 and (0).1 in 107
  have eq167 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq107 eq130 -- superposition 130,107, 107 into 130, unify on (0).2 in 107 and (0).2 in 130
  subsumption eq167 eq156


@[equational_result]
theorem Equation688_implies_Equation125 (G : Type*) [Magma G] (h : Equation688 G) : Equation125 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq20 : sK0 ≠ (sK1 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 eq19


@[equational_result]
theorem Equation688_implies_Equation1719 (G : Type*) [Magma G] (h : Equation688 G) : Equation1719 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq22 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 eq19


@[equational_result]
theorem Equation688_implies_Equation2 (G : Type*) [Magma G] (h : Equation688 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq18 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq21 eq18


@[equational_result]
theorem Equation688_implies_Equation2294 (G : Type*) [Magma G] (h : Equation688 G) : Equation2294 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2 in 14
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq30 (X0 : G) : sK0 ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2.1 in 15
  subsumption eq30 eq19


@[equational_result]
theorem Equation688_implies_Equation2504 (G : Type*) [Magma G] (h : Equation688 G) : Equation2504 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2 in 14
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq30 (X0 : G) : sK0 ≠ ((X0 ◇ sK1) ◇ sK1) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2.1 in 15
  subsumption eq30 eq19


@[equational_result]
theorem Equation689_implies_Equation1350 (G : Type*) [Magma G] (h : Equation689 G) : Equation1350 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK0) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 X5 : G) : (X5 ◇ (X1 ◇ X2)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq20 (X1 X2 : G) : X1 = X2 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1 in 12
  have eq21 : sK0 ≠ ((sK2 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq21 eq20


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
theorem Equation691_implies_Equation1976 (G : Type*) [Magma G] (h : Equation691 G) : Equation1976 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X0) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X1)) = ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq15 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X1) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X1)) = (X2 ◇ (X3 ◇ X2)) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq40 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) = ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq12 eq17 -- superposition 17,12, 12 into 17, unify on (0).2 in 12 and (0).1.1 in 17
  have eq52 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = (X2 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.2 in 9
  have eq54 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) = X2 := superpose eq9 eq40 -- forward demodulation 40,9
  have eq62 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq54 eq31 -- backward demodulation 31,54
  have eq66 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq9 eq52 -- forward demodulation 52,9
  have eq68 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq66 eq62 -- backward demodulation 62,66
  have eq70 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) := superpose eq66 eq15 -- backward demodulation 15,66
  have eq71 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq70 eq68 -- backward demodulation 68,70
  have eq72 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X1)) = X0 := superpose eq71 eq9 -- backward demodulation 9,71
  have eq75 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X1)) = X2 := superpose eq71 eq54 -- backward demodulation 54,71
  have eq81 (X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = X2 := superpose eq75 eq19 -- backward demodulation 19,75
  have eq82 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq81 eq10 -- backward demodulation 10,81
  have eq84 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq81 eq81 -- superposition 81,81, 81 into 81, unify on (0).2 in 81 and (0).1.2 in 81
  have eq90 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq84 eq72 -- backward demodulation 72,84
  have eq101 (X2 X3 : G) : X2 = X3 := superpose eq90 eq90 -- superposition 90,90, 90 into 90, unify on (0).2 in 90 and (0).1 in 90
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq90 eq82 -- superposition 82,90, 90 into 82, unify on (0).2 in 90 and (0).2 in 82
  subsumption eq106 eq101


@[equational_result]
theorem Equation693_implies_Equation927 (G : Type*) [Magma G] (h : Equation693 G) : Equation927 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X1 X2 X5 : G) : (X1 ◇ (X5 ◇ X2)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ (sK1 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq20 (X2 X3 : G) : X2 = X3 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq23 (X0 : G) : sK0 ≠ (X0 ◇ sK0) := superpose eq20 eq16 -- superposition 16,20, 20 into 16, unify on (0).2 in 20 and (0).2.1 in 16
  subsumption eq23 eq20


@[equational_result]
theorem Equation694_implies_Equation672 (G : Type*) [Magma G] (h : Equation694 G) : Equation672 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation698_implies_Equation1535 (G : Type*) [Magma G] (h : Equation698 G) : Equation1535 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X1 X4 X5 : G) : (X4 ◇ (X5 ◇ (X1 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq73 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1.2 in 11
  have eq78 (X0 : G) : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ (X0 ◇ sK0))) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2.2.2 in 10
  subsumption eq78 eq73


@[equational_result]
theorem Equation703_implies_Equation1434 (G : Type*) [Magma G] (h : Equation703 G) : Equation1434 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq14 (X0 : G) : ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq15 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq26 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).1.2 in 14
  have eq61 (X0 : G) : sK0 ≠ ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ sK0))) := superpose eq24 eq10 -- superposition 10,24, 24 into 10, unify on (0).2 in 24 and (0).2.2 in 10
  subsumption eq61 eq26


@[equational_result]
theorem Equation703_implies_Equation4307 (G : Type*) [Magma G] (h : Equation703 G) : Equation4307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq21 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq61 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (X0 ◇ sK1)) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq61 eq21


@[equational_result]
theorem Equation705_implies_Equation2901 (G : Type*) [Magma G] (h : Equation705 G) : Equation2901 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq16 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1 in 11
  have eq18 (X0 X1 : G) : sK0 ≠ ((X0 ◇ (X0 ◇ X1)) ◇ sK2) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2.1 in 10
  subsumption eq18 eq16


@[equational_result]
theorem Equation708_implies_Equation1976 (G : Type*) [Magma G] (h : Equation708 G) : Equation1976 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq16 (X1 X3 : G) : X1 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq25 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq25 eq16


@[equational_result]
theorem Equation709_implies_Equation1539 (G : Type*) [Magma G] (h : Equation709 G) : Equation1539 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq29 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1 in 16
  have eq45 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq45 eq29


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
theorem Equation714_implies_Equation4435 (G : Type*) [Magma G] (h : Equation714 G) : Equation4435 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq15 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) = (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq19 (X0 X1 : G) : (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq11 eq15 -- forward demodulation 15,11
  have eq20 (X0 X1 : G) : (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq11 eq19 -- forward demodulation 19,11
  have eq21 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) := superpose eq12 eq20 -- forward demodulation 20,12
  have eq25 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq21 eq12 -- superposition 12,21, 21 into 12, unify on (0).2 in 21 and (0).1.2 in 12
  have eq46 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq25 eq10 -- superposition 10,25, 25 into 10, unify on (0).2 in 25 and (0).2 in 10
  subsumption eq46 rfl


@[equational_result]
theorem Equation719_implies_Equation78 (G : Type*) [Magma G] (h : Equation719 G) : Equation78 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


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
theorem Equation724_implies_Equation2365 (G : Type*) [Magma G] (h : Equation724 G) : Equation2365 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X3 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq24 (X1 X2 X3 X4 : G) : (X3 ◇ ((X4 ◇ (X1 ◇ X2)) ◇ X3)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq32 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ X0) := superpose eq24 eq13 -- backward demodulation 13,24
  have eq73 (X2 X3 X4 : G) : (X3 ◇ (X4 ◇ X3)) = X2 := superpose eq9 eq32 -- superposition 32,9, 9 into 32, unify on (0).2 in 9 and (0).2 in 32
  have eq107 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X1 ◇ X0)) := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2 in 10
  subsumption eq107 eq73


@[equational_result]
theorem Equation727_implies_Equation832 (G : Type*) [Magma G] (h : Equation727 G) : Equation832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X5)) = ((X1 ◇ (X1 ◇ X3)) ◇ ((X4 ◇ (X1 ◇ (X1 ◇ X3))) ◇ X5)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X4)) = (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X4)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq19 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X3))) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq22 (X0 X1 X2 X3 X5 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X5)) = ((X1 ◇ X3) ◇ ((X1 ◇ X3) ◇ X5)) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq47 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ X3)) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ X3)) ◇ X4))) = X4 := superpose eq11 eq19 -- superposition 19,11, 11 into 19, unify on (0).2 in 11 and (0).1.1 in 19
  have eq51 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ X3)) = ((X4 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3)) := superpose eq11 eq19 -- superposition 19,11, 11 into 19, unify on (0).2 in 11 and (0).1.2.2 in 19
  have eq53 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq54 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X4 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X3) := superpose eq11 eq19 -- superposition 19,11, 11 into 19, unify on (0).2 in 11 and (0).1.2 in 19
  have eq63 (X2 X3 X4 : G) : (X3 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4))) = X4 := superpose eq22 eq47 -- forward demodulation 47,22
  have eq65 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ X3)) = (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3)) := superpose eq54 eq51 -- backward demodulation 51,54
  have eq66 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3))) = X3 := superpose eq65 eq11 -- backward demodulation 11,65
  have eq78 (X0 X1 X2 X3 X4 X5 : G) : ((((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X4)) ◇ (X4 ◇ ((((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X5))) = X5 := superpose eq12 eq66 -- superposition 66,12, 12 into 66, unify on (0).2 in 12 and (0).1.1.2.1 in 66
  have eq98 (X3 X4 X5 : G) : ((X3 ◇ (X3 ◇ X4)) ◇ (X4 ◇ ((X3 ◇ (X3 ◇ X4)) ◇ X5))) = X5 := superpose eq16 eq78 -- forward demodulation 78,16
  have eq113 (X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X4 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) := superpose eq19 eq53 -- superposition 53,19, 19 into 53, unify on (0).2 in 19 and (0).1.1 in 53
  have eq147 (X0 : G) : sK0 ≠ (sK0 ◇ ((X0 ◇ sK0) ◇ (sK0 ◇ sK0))) := superpose eq53 eq10 -- superposition 10,53, 53 into 10, unify on (0).2 in 53 and (0).2.2 in 10
  have eq352 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq98 eq9 -- superposition 9,98, 98 into 9, unify on (0).2 in 98 and (0).1.2.2 in 9
  have eq396 (X2 X3 X4 : G) : (X3 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X4))) = X4 := superpose eq352 eq63 -- backward demodulation 63,352
  have eq437 (X2 X3 X4 : G) : (X3 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X4))) = X4 := superpose eq113 eq396 -- forward demodulation 396,113
  have eq503 : sK0 ≠ sK0 := superpose eq437 eq147 -- superposition 147,437, 437 into 147, unify on (0).2 in 437 and (0).2 in 147
  subsumption eq503 rfl


@[equational_result]
theorem Equation727_implies_Equation964 (G : Type*) [Magma G] (h : Equation727 G) : Equation964 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X5)) = ((X1 ◇ (X1 ◇ X3)) ◇ ((X4 ◇ (X1 ◇ (X1 ◇ X3))) ◇ X5)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X4)) = (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X4)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq20 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X3))) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq22 (X0 X1 X2 X3 X5 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X5)) = ((X1 ◇ X3) ◇ ((X1 ◇ X3) ◇ X5)) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq47 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ X3)) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ X3)) ◇ X4))) = X4 := superpose eq11 eq20 -- superposition 20,11, 11 into 20, unify on (0).2 in 11 and (0).1.1 in 20
  have eq51 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ X3)) = ((X4 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3)) := superpose eq11 eq20 -- superposition 20,11, 11 into 20, unify on (0).2 in 11 and (0).1.2.2 in 20
  have eq53 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq9 eq20 -- superposition 20,9, 9 into 20, unify on (0).2 in 9 and (0).1.2 in 20
  have eq54 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X4 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X3) := superpose eq11 eq20 -- superposition 20,11, 11 into 20, unify on (0).2 in 11 and (0).1.2 in 20
  have eq63 (X2 X3 X4 : G) : (X3 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4))) = X4 := superpose eq22 eq47 -- forward demodulation 47,22
  have eq65 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ X3)) = (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3)) := superpose eq54 eq51 -- backward demodulation 51,54
  have eq66 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3))) = X3 := superpose eq65 eq11 -- backward demodulation 11,65
  have eq78 (X0 X1 X2 X3 X4 X5 : G) : ((((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X4)) ◇ (X4 ◇ ((((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X5))) = X5 := superpose eq12 eq66 -- superposition 66,12, 12 into 66, unify on (0).2 in 12 and (0).1.1.2.1 in 66
  have eq98 (X3 X4 X5 : G) : ((X3 ◇ (X3 ◇ X4)) ◇ (X4 ◇ ((X3 ◇ (X3 ◇ X4)) ◇ X5))) = X5 := superpose eq16 eq78 -- forward demodulation 78,16
  have eq113 (X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X4 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) := superpose eq20 eq53 -- superposition 53,20, 20 into 53, unify on (0).2 in 20 and (0).1.1 in 53
  have eq135 (X0 : G) : sK0 ≠ (sK1 ◇ ((X0 ◇ sK1) ◇ (sK1 ◇ sK0))) := superpose eq53 eq10 -- superposition 10,53, 53 into 10, unify on (0).2 in 53 and (0).2.2 in 10
  have eq342 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq98 eq9 -- superposition 9,98, 98 into 9, unify on (0).2 in 98 and (0).1.2.2 in 9
  have eq387 (X2 X3 X4 : G) : (X3 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X4))) = X4 := superpose eq342 eq63 -- backward demodulation 63,342
  have eq430 (X2 X3 X4 : G) : (X3 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X4))) = X4 := superpose eq113 eq387 -- forward demodulation 387,113
  have eq523 : sK0 ≠ sK0 := superpose eq430 eq135 -- superposition 135,430, 430 into 135, unify on (0).2 in 430 and (0).2 in 135
  subsumption eq523 rfl


@[equational_result]
theorem Equation72_implies_Equation909 (G : Type*) [Magma G] (h : Equation72 G) : Equation909 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).1.2.2 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1.2 in 25
  have eq192 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) := superpose eq15 eq39 -- superposition 39,15, 15 into 39, unify on (0).2 in 15 and (0).2.2.2.2 in 39
  have eq253 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq57 eq192 -- forward demodulation 192,57
  have eq254 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq253 eq10 -- backward demodulation 10,253
  subsumption eq254 eq9


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
theorem Equation741_implies_Equation1522 (G : Type*) [Magma G] (h : Equation741 G) : Equation1522 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X2 ◇ X2) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq23 (X0 X1 : G) : sK0 ≠ (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq23 eq17


@[equational_result]
theorem Equation744_implies_Equation1603 (G : Type*) [Magma G] (h : Equation744 G) : Equation1603 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq20 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X2 ◇ X0))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq70 (X0 : G) : sK0 ≠ (X0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq70 eq20


@[equational_result]
theorem Equation745_implies_Equation2704 (G : Type*) [Magma G] (h : Equation745 G) : Equation2704 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X2 X3 : G) : X2 = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq27 (X0 X1 : G) : sK0 ≠ (((X0 ◇ X1) ◇ X1) ◇ X0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq27 eq18


@[equational_result]
theorem Equation746_implies_Equation4332 (G : Type*) [Magma G] (h : Equation746 G) : Equation4332 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq33 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X1 ◇ (X2 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq76 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq33 eq10 -- superposition 10,33, 33 into 10, unify on (0).2 in 33 and (0).2 in 10
  subsumption eq76 eq33


@[equational_result]
theorem Equation748_implies_Equation782 (G : Type*) [Magma G] (h : Equation748 G) : Equation782 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X3 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq32 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ ((sK0 ◇ X0) ◇ sK0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq32 eq9


@[equational_result]
theorem Equation749_implies_Equation2865 (G : Type*) [Magma G] (h : Equation749 G) : Equation2865 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq21 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  subsumption eq21 eq13


@[equational_result]
theorem Equation749_implies_Equation556 (G : Type*) [Magma G] (h : Equation749 G) : Equation556 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq213 : sK0 ≠ sK0 := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq213 rfl


@[equational_result]
theorem Equation749_implies_Equation639 (G : Type*) [Magma G] (h : Equation749 G) : Equation639 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq21 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := superpose eq20 eq10 -- backward demodulation 10,20
  have eq22 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := superpose eq20 eq21 -- forward demodulation 21,20
  subsumption eq22 eq18


@[equational_result]
theorem Equation750_implies_Equation751 (G : Type*) [Magma G] (h : Equation750 G) : Equation751 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ sK3))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X2 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X2)) = X0 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq24 (X3 X4 : G) : X3 = X4 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1 in 13
  have eq39 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ X0)) := superpose eq24 eq10 -- superposition 10,24, 24 into 10, unify on (0).2 in 24 and (0).2.2.2 in 10
  subsumption eq39 eq24


@[equational_result]
theorem Equation751_implies_Equation2932 (G : Type*) [Magma G] (h : Equation751 G) : Equation2932 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK2)) ◇ sK3) ◇ sK1) := mod_symm nh
  have eq13 (X1 X2 X4 : G) : (X4 ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X2 X4 : G) : X2 = X4 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq20 (X0 : G) : sK0 ≠ (X0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq20 eq14


@[equational_result]
theorem Equation751_implies_Equation693 (G : Type*) [Magma G] (h : Equation751 G) : Equation693 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK2 ◇ sK1) ◇ sK3))) := mod_symm nh
  have eq13 (X1 X2 X4 : G) : (X4 ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X2 X4 : G) : X2 = X4 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq20 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ X0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.2 in 10
  subsumption eq20 eq14


@[equational_result]
theorem Equation755_implies_Equation677 (G : Type*) [Magma G] (h : Equation755 G) : Equation677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq13 (X1 X2 X4 : G) : (X4 ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X2 X4 : G) : X2 = X4 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq21 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ X0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.2 in 10
  subsumption eq21 eq15


@[equational_result]
theorem Equation757_implies_Equation1510 (G : Type*) [Magma G] (h : Equation757 G) : Equation1510 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 : G) : (X3 ◇ X1) = (X2 ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X2 ◇ X1))) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq88 (X0 : G) : sK0 ≠ ((X0 ◇ sK0) ◇ (sK2 ◇ (sK3 ◇ sK0))) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1 in 10
  subsumption eq88 eq21


@[equational_result]
theorem Equation758_implies_Equation671 (G : Type*) [Magma G] (h : Equation758 G) : Equation671 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq25 (X0 X1 : G) : sK0 ≠ (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq25 eq17


@[equational_result]
theorem Equation761_implies_Equation694 (G : Type*) [Magma G] (h : Equation761 G) : Equation694 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK2 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq22 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X2 ◇ X1))) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq108 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ sK0))) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq108 eq22


@[equational_result]
theorem Equation765_implies_Equation4023 (G : Type*) [Magma G] (h : Equation765 G) : Equation4023 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq76 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq18 eq13 -- superposition 13,18, 18 into 13, unify on (0).2 in 18 and (0).2.1 in 13
  have eq561 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq76 eq10 -- superposition 10,76, 76 into 10, unify on (0).2 in 76 and (0).2 in 10
  subsumption eq561 rfl


@[equational_result]
theorem Equation765_implies_Equation4146 (G : Type*) [Magma G] (h : Equation765 G) : Equation4146 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X2 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq36 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = X2 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.2 in 11
  have eq142 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).1.2 in 36
  have eq1096 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq142 eq10 -- superposition 10,142, 142 into 10, unify on (0).2 in 142 and (0).2 in 10
  subsumption eq1096 rfl


@[equational_result]
theorem Equation765_implies_Equation4226 (G : Type*) [Magma G] (h : Equation765 G) : Equation4226 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK2) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq76 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq18 eq13 -- superposition 13,18, 18 into 13, unify on (0).2 in 18 and (0).2.1 in 13
  have eq104 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X1 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.1 in 13
  have eq1200 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK1) := superpose eq104 eq10 -- superposition 10,104, 104 into 10, unify on (0).2 in 104 and (0).2 in 10
  subsumption eq1200 eq76


@[equational_result]
theorem Equation765_implies_Equation4362 (G : Type*) [Magma G] (h : Equation765 G) : Equation4362 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X2 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq36 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = X2 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.2 in 11
  have eq69 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) = X2 := superpose eq13 eq18 -- superposition 18,13, 13 into 18, unify on (0).2 in 13 and (0).1.2 in 18
  have eq141 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) = X2 := superpose eq13 eq36 -- superposition 36,13, 13 into 36, unify on (0).2 in 13 and (0).1.2 in 36
  have eq795 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq69 eq141 -- superposition 141,69, 69 into 141, unify on (0).2 in 69 and (0).1.2.2 in 141
  have eq5051 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq795 eq10 -- superposition 10,795, 795 into 10, unify on (0).2 in 795 and (0).2 in 10
  subsumption eq5051 rfl


@[equational_result]
theorem Equation765_implies_Equation731 (G : Type*) [Magma G] (h : Equation765 G) : Equation731 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK2 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1.2 in 13
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq69 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) = X2 := superpose eq13 eq18 -- superposition 18,13, 13 into 18, unify on (0).2 in 13 and (0).1.2 in 18
  have eq84 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X5)) = (X4 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X5)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.1 in 12
  have eq100 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X1 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.1 in 13
  have eq107 (X0 X1 X2 X3 X5 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X5)) = (X1 ◇ ((X2 ◇ X3) ◇ X5)) := superpose eq12 eq84 -- forward demodulation 84,12
  have eq116 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X5)) = (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X5)) := superpose eq100 eq107 -- backward demodulation 107,100
  have eq122 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X5)) = (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X5)) := superpose eq100 eq116 -- forward demodulation 116,100
  have eq233 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X3) := superpose eq69 eq13 -- superposition 13,69, 69 into 13, unify on (0).2 in 69 and (0).2.1.2 in 13
  have eq257 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X4) = (((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ X4) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2.1.1.2 in 14
  have eq287 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ ((X3 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2)) ◇ X4))) = X4 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2 in 9
  have eq304 (X0 X1 X2 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X4) = ((X2 ◇ X1) ◇ X4) := superpose eq233 eq257 -- forward demodulation 257,233
  have eq350 (X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X4))) = X4 := superpose eq304 eq287 -- forward demodulation 287,304
  have eq351 (X2 X3 X4 : G) : (X3 ◇ (X3 ◇ ((X2 ◇ X2) ◇ X4))) = X4 := superpose eq122 eq350 -- forward demodulation 350,122
  have eq1505 : sK0 ≠ sK0 := superpose eq351 eq10 -- superposition 10,351, 351 into 10, unify on (0).2 in 351 and (0).2 in 10
  subsumption eq1505 rfl


@[equational_result]
theorem Equation774_implies_Equation1581 (G : Type*) [Magma G] (h : Equation774 G) : Equation1581 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X2)) = (X3 ◇ (X0 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X2)) = (X3 ◇ (X0 ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2)))) = (X3 ◇ (X4 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2)))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq18 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ (X1 ◇ X2))) = (X0 ◇ (X3 ◇ ((X3 ◇ X2) ◇ X2))) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq33 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2)))) = (X3 ◇ X2) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq34 (X0 X2 X3 : G) : (X0 ◇ X2) = (X3 ◇ X2) := superpose eq9 eq33 -- forward demodulation 33,9
  have eq36 (X1 X2 X4 X5 : G) : (X4 ◇ (X5 ◇ (X1 ◇ X2))) = X2 := superpose eq9 eq18 -- forward demodulation 18,9
  have eq60 (X0 : G) : sK0 ≠ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0))) := superpose eq34 eq10 -- superposition 10,34, 34 into 10, unify on (0).2 in 34 and (0).2 in 10
  subsumption eq60 eq36


@[equational_result]
theorem Equation775_implies_Equation2928 (G : Type*) [Magma G] (h : Equation775 G) : Equation2928 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK2)) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = (X3 ◇ (X0 ◇ (X2 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) = X1 := superpose eq18 eq13 -- backward demodulation 13,18
  have eq23 : sK0 ≠ ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ sK1) := superpose eq18 eq10 -- backward demodulation 10,18
  have eq123 (X0 : G) : sK0 ≠ ((X0 ◇ ((X0 ◇ sK0) ◇ sK1)) ◇ sK1) := superpose eq11 eq23 -- superposition 23,11, 11 into 23, unify on (0).2 in 11 and (0).2.1 in 23
  subsumption eq123 eq22


@[equational_result]
theorem Equation776_implies_Equation792 (G : Type*) [Magma G] (h : Equation776 G) : Equation792 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK3 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq24 (X3 X4 : G) : X3 = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq81 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ X0)) := superpose eq24 eq10 -- superposition 10,24, 24 into 10, unify on (0).2 in 24 and (0).2.2.2 in 10
  subsumption eq81 eq24


@[equational_result]
theorem Equation782_implies_Equation735 (G : Type*) [Magma G] (h : Equation782 G) : Equation735 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK2 ◇ sK3) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq35 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ sK0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq35 eq9


@[equational_result]
theorem Equation78_implies_Equation757 (G : Type*) [Magma G] (h : Equation78 G) : Equation757 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK1 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq22 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (X0 ◇ sK0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2.2 in 10
  subsumption eq22 eq13


@[equational_result]
theorem Equation791_implies_Equation943 (G : Type*) [Magma G] (h : Equation791 G) : Equation943 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X3)) = (X4 ◇ (X5 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X3))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq14 (X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X3)) = (X4 ◇ (X5 ◇ X3)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq65 (X0 X1 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ ((X1 ◇ sK0) ◇ sK0))) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2 in 10
  subsumption eq65 eq9


@[equational_result]
theorem Equation792_implies_Equation1923 (G : Type*) [Magma G] (h : Equation792 G) : Equation1923 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq13 (X0 X2 X3 X4 : G) : (((X3 ◇ X4) ◇ X0) ◇ X4) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X3 X4 : G) : X3 = X4 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1 in 13
  have eq28 (X0 X1 X2 : G) : sK0 ≠ (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq28 eq20


@[equational_result]
theorem Equation796_implies_Equation938 (G : Type*) [Magma G] (h : Equation796 G) : Equation938 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X2 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X3 X4 X5 : G) : (X5 ◇ X4) = (X3 ◇ X4) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq24 (X1 X2 X3 X4 : G) : (X1 ◇ (X4 ◇ (X3 ◇ X2))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq89 (X0 : G) : sK0 ≠ (X0 ◇ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK0))) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq89 eq24


@[equational_result]
theorem Equation801_implies_Equation82 (G : Type*) [Magma G] (h : Equation801 G) : Equation82 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X3 ◇ X2) ◇ X4)) = (X5 ◇ (X1 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ X3) = (X4 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X3 X4 X5 : G) : (X3 ◇ X4) = (X5 ◇ X4) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq41 (X1 X2 X3 X4 X5 X6 X7 : G) : (X6 ◇ (X7 ◇ (X2 ◇ X3))) = (X1 ◇ (X4 ◇ ((X5 ◇ X4) ◇ X3))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq76 (X2 X3 X6 X7 : G) : (X6 ◇ (X7 ◇ (X2 ◇ X3))) = X3 := superpose eq9 eq41 -- forward demodulation 41,9
  have eq111 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (X0 ◇ sK0))) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2.2.2 in 10
  subsumption eq111 eq76


@[equational_result]
theorem Equation806_implies_Equation1465 (G : Type*) [Magma G] (h : Equation806 G) : Equation1465 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ (X2 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation811_implies_Equation912 (G : Type*) [Magma G] (h : Equation811 G) : Equation912 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X4 X5 X6 X7 : G) : (X5 ◇ (X6 ◇ (X4 ◇ X7))) = X7 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


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
theorem Equation821_implies_Equation100 (G : Type*) [Magma G] (h : Equation821 G) : Equation100 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ ((X3 ◇ X3) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


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
theorem Equation824_implies_Equation1031 (G : Type*) [Magma G] (h : Equation824 G) : Equation1031 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X3 : G) : (X0 ◇ ((X0 ◇ X3) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq25 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq25 rfl


@[equational_result]
theorem Equation824_implies_Equation1225 (G : Type*) [Magma G] (h : Equation824 G) : Equation1225 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X3 : G) : (X0 ◇ ((X0 ◇ X3) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq19 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq19 eq12


@[equational_result]
theorem Equation824_implies_Equation1631 (G : Type*) [Magma G] (h : Equation824 G) : Equation1631 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X3 : G) : (X0 ◇ ((X0 ◇ X3) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq19 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq19 eq12


@[equational_result]
theorem Equation824_implies_Equation2446 (G : Type*) [Magma G] (h : Equation824 G) : Equation2446 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X3 : G) : (X0 ◇ ((X0 ◇ X3) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq24 : sK0 ≠ sK0 := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).2 in 13
  subsumption eq24 rfl


@[equational_result]
theorem Equation824_implies_Equation3458 (G : Type*) [Magma G] (h : Equation824 G) : Equation3458 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X3 : G) : (X0 ◇ ((X0 ◇ X3) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq24 : sK0 ≠ sK0 := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).2 in 13
  subsumption eq24 rfl


@[equational_result]
theorem Equation824_implies_Equation424 (G : Type*) [Magma G] (h : Equation824 G) : Equation424 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq19 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).1.2 in 9
  have eq38 : sK0 ≠ sK0 := superpose eq23 eq19 -- superposition 19,23, 23 into 19, unify on (0).2 in 23 and (0).2 in 19
  subsumption eq38 rfl


@[equational_result]
theorem Equation827_implies_Equation102 (G : Type*) [Magma G] (h : Equation827 G) : Equation102 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ ((X3 ◇ X0) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation827_implies_Equation415 (G : Type*) [Magma G] (h : Equation827 G) : Equation415 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ ((X3 ◇ X0) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.1 in 12
  have eq17 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq39 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.2.1 in 9
  have eq89 : sK0 ≠ sK0 := superpose eq39 eq10 -- superposition 10,39, 39 into 10, unify on (0).2 in 39 and (0).2 in 10
  subsumption eq89 rfl


@[equational_result]
theorem Equation829_implies_Equation1032 (G : Type*) [Magma G] (h : Equation829 G) : Equation1032 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq59 (X0 X1 X4 : G) : (X4 ◇ ((X4 ◇ (X0 ◇ X1)) ◇ X0)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.2 in 12
  have eq120 : sK0 ≠ sK0 := superpose eq59 eq10 -- superposition 10,59, 59 into 10, unify on (0).2 in 59 and (0).2 in 10
  subsumption eq120 rfl


@[equational_result]
theorem Equation829_implies_Equation423 (G : Type*) [Magma G] (h : Equation829 G) : Equation423 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation831_implies_Equation1227 (G : Type*) [Magma G] (h : Equation831 G) : Equation1227 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X4 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq19 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq19 eq12


@[equational_result]
theorem Equation831_implies_Equation1633 (G : Type*) [Magma G] (h : Equation831 G) : Equation1633 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X4 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq19 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq19 eq12


@[equational_result]
theorem Equation831_implies_Equation2452 (G : Type*) [Magma G] (h : Equation831 G) : Equation2452 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X4 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq24 : sK0 ≠ sK0 := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  subsumption eq24 rfl


@[equational_result]
theorem Equation831_implies_Equation3460 (G : Type*) [Magma G] (h : Equation831 G) : Equation3460 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X4 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq24 : sK0 ≠ sK0 := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  subsumption eq24 rfl


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
theorem Equation837_implies_Equation105 (G : Type*) [Magma G] (h : Equation837 G) : Equation105 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ ((X0 ◇ X3) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation837_implies_Equation107 (G : Type*) [Magma G] (h : Equation837 G) : Equation107 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X3 : G) : (X3 ◇ ((X0 ◇ X3) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.1 in 12
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq17 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X0 ◇ X3)) = ((X0 ◇ (X0 ◇ X3)) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq72 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).1 in 14
  have eq73 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).1.2 in 12
  have eq251 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = ((X1 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq73 eq17 -- superposition 17,73, 73 into 17, unify on (0).2 in 73 and (0).2.2 in 17
  have eq712 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq72 eq251 -- superposition 251,72, 72 into 251, unify on (0).2 in 72 and (0).2.2 in 251
  have eq3261 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq712 eq9 -- superposition 9,712, 712 into 9, unify on (0).2 in 712 and (0).1.2 in 9
  have eq3617 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X1 := superpose eq3261 eq9 -- superposition 9,3261, 3261 into 9, unify on (0).2 in 3261 and (0).1.2 in 9
  have eq4043 : sK0 ≠ sK0 := superpose eq3617 eq10 -- superposition 10,3617, 3617 into 10, unify on (0).2 in 3617 and (0).2 in 10
  subsumption eq4043 rfl


@[equational_result]
theorem Equation839_implies_Equation1067 (G : Type*) [Magma G] (h : Equation839 G) : Equation1067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation839_implies_Equation1229 (G : Type*) [Magma G] (h : Equation839 G) : Equation1229 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X3) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq29 (X0 X1 X4 : G) : (X4 ◇ (((X0 ◇ X1) ◇ X4) ◇ X1)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.1 in 12
  have eq126 : sK0 ≠ sK0 := superpose eq29 eq10 -- superposition 10,29, 29 into 10, unify on (0).2 in 29 and (0).2 in 10
  subsumption eq126 rfl


@[equational_result]
theorem Equation839_implies_Equation1249 (G : Type*) [Magma G] (h : Equation839 G) : Equation1249 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X3) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq29 (X0 X1 X4 : G) : (X4 ◇ (((X0 ◇ X1) ◇ X4) ◇ X1)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.1 in 12
  have eq140 : sK0 ≠ sK0 := superpose eq29 eq10 -- superposition 10,29, 29 into 10, unify on (0).2 in 29 and (0).2 in 10
  subsumption eq140 rfl


@[equational_result]
theorem Equation839_implies_Equation1260 (G : Type*) [Magma G] (h : Equation839 G) : Equation1260 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X3) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq29 (X0 X1 X4 : G) : (X4 ◇ (((X0 ◇ X1) ◇ X4) ◇ X1)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.1 in 12
  have eq140 : sK0 ≠ sK0 := superpose eq29 eq10 -- superposition 10,29, 29 into 10, unify on (0).2 in 29 and (0).2 in 10
  subsumption eq140 rfl


@[equational_result]
theorem Equation841_implies_Equation1261 (G : Type*) [Magma G] (h : Equation841 G) : Equation1261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ sK3)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X4) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq29 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq29 rfl


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
theorem Equation847_implies_Equation108 (G : Type*) [Magma G] (h : Equation847 G) : Equation108 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


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
  have eq2949 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X1 := superpose eq1973 eq9 -- superposition 9,1973, 1973 into 9, unify on (0).2 in 1973 and (0).1.2 in 9
  have eq3357 : sK0 ≠ sK0 := superpose eq2949 eq10 -- superposition 10,2949, 2949 into 10, unify on (0).2 in 2949 and (0).2 in 10
  subsumption eq3357 rfl


@[equational_result]
theorem Equation849_implies_Equation851 (G : Type*) [Magma G] (h : Equation849 G) : Equation851 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X3 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X3)) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq32 (X0 X3 X4 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X4)) = X3 := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2.1 in 14
  have eq78 : sK0 ≠ sK0 := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2 in 10
  subsumption eq78 rfl


@[equational_result]
theorem Equation851_implies_Equation109 (G : Type*) [Magma G] (h : Equation851 G) : Equation109 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq29 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation851_implies_Equation1227 (G : Type*) [Magma G] (h : Equation851 G) : Equation1227 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq41 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq41 rfl


@[equational_result]
theorem Equation851_implies_Equation1250 (G : Type*) [Magma G] (h : Equation851 G) : Equation1250 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq47 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation851_implies_Equation1254 (G : Type*) [Magma G] (h : Equation851 G) : Equation1254 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq47 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation851_implies_Equation1255 (G : Type*) [Magma G] (h : Equation851 G) : Equation1255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq47 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation851_implies_Equation1257 (G : Type*) [Magma G] (h : Equation851 G) : Equation1257 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq47 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation852_implies_Equation52 (G : Type*) [Magma G] (h : Equation852 G) : Equation52 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation853_implies_Equation456 (G : Type*) [Magma G] (h : Equation853 G) : Equation456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X3 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0)) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.2 in 9
  have eq37 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2.1 in 14
  have eq43 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq11 eq37 -- forward demodulation 37,11
  have eq99 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.2 in 11
  have eq995 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = (((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.1.2 in 99
  have eq1065 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq11 eq995 -- forward demodulation 995,11
  have eq1152 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq1065 eq1065 -- superposition 1065,1065, 1065 into 1065, unify on (0).2 in 1065 and (0).2.2 in 1065
  have eq1211 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq1152 eq9 -- backward demodulation 9,1152
  have eq1254 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq1211 eq11 -- backward demodulation 11,1211
  have eq1315 : sK0 ≠ (sK0 ◇ sK1) := superpose eq1211 eq10 -- backward demodulation 10,1211
  subsumption eq1315 eq1254


@[equational_result]
theorem Equation854_implies_Equation1031 (G : Type*) [Magma G] (h : Equation854 G) : Equation1031 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq32 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1 in 12
  have eq83 : sK0 ≠ sK0 := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2 in 10
  subsumption eq83 rfl


@[equational_result]
theorem Equation854_implies_Equation1035 (G : Type*) [Magma G] (h : Equation854 G) : Equation1035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq38 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.2.2 in 9
  have eq192 : sK0 ≠ sK0 := superpose eq38 eq10 -- superposition 10,38, 38 into 10, unify on (0).2 in 38 and (0).2 in 10
  subsumption eq192 rfl


@[equational_result]
theorem Equation854_implies_Equation1228 (G : Type*) [Magma G] (h : Equation854 G) : Equation1228 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X4 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))))) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.2.1 in 11
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq32 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1 in 12
  have eq54 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3)))) = ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3)))) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq62 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq54 -- forward demodulation 54,9
  have eq65 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := superpose eq62 eq10 -- backward demodulation 10,62
  subsumption eq65 eq32


@[equational_result]
theorem Equation854_implies_Equation1231 (G : Type*) [Magma G] (h : Equation854 G) : Equation1231 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X4 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))))) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.2.1 in 11
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq32 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1 in 12
  have eq54 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3)))) = ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3)))) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq62 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq54 -- forward demodulation 54,9
  have eq65 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := superpose eq62 eq10 -- backward demodulation 10,62
  subsumption eq65 eq32


@[equational_result]
theorem Equation854_implies_Equation378 (G : Type*) [Magma G] (h : Equation854 G) : Equation378 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X4 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))))) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.2.1 in 11
  have eq54 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3)))) = ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3)))) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq62 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq54 -- forward demodulation 54,9
  have eq137 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq62 eq10 -- superposition 10,62, 62 into 10, unify on (0).2 in 62 and (0).2 in 10
  subsumption eq137 rfl


@[equational_result]
theorem Equation854_implies_Equation430 (G : Type*) [Magma G] (h : Equation854 G) : Equation430 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq39 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.2.1 in 9
  have eq259 : sK0 ≠ sK0 := superpose eq39 eq10 -- superposition 10,39, 39 into 10, unify on (0).2 in 39 and (0).2 in 10
  subsumption eq259 rfl


@[equational_result]
theorem Equation856_implies_Equation55 (G : Type*) [Magma G] (h : Equation856 G) : Equation55 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation864_implies_Equation378 (G : Type*) [Magma G] (h : Equation864 G) : Equation378 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X4))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 (X0 X3 : G) : (X3 ◇ X0) = ((X3 ◇ X0) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq36 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq36 rfl


@[equational_result]
theorem Equation864_implies_Equation661 (G : Type*) [Magma G] (h : Equation864 G) : Equation661 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK3) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X4))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation869_implies_Equation811 (G : Type*) [Magma G] (h : Equation869 G) : Equation811 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK3 ◇ sK4) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq19 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq38 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2 in 13
  subsumption eq38 eq19


@[equational_result]
theorem Equation874_implies_Equation3114 (G : Type*) [Magma G] (h : Equation874 G) : Equation3114 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK1) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X2 : G) : X1 = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq19 (X0 : G) : sK0 ≠ (((X0 ◇ X0) ◇ X0) ◇ sK2) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq19 eq14


@[equational_result]
theorem Equation876_implies_Equation2984 (G : Type*) [Magma G] (h : Equation876 G) : Equation2984 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK0)) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ X1) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq16 (X1 X2 : G) : X1 = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq21 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK2) ◇ sK3) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq29 (X0 : G) : sK0 ≠ (X0 ◇ sK3) := superpose eq16 eq21 -- superposition 21,16, 16 into 21, unify on (0).2 in 16 and (0).2.1 in 21
  subsumption eq29 eq16


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
theorem Equation884_implies_Equation758 (G : Type*) [Magma G] (h : Equation884 G) : Equation758 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK1 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq35 (X1 X3 : G) : X1 = X3 := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).1 in 15
  have eq53 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2.2 in 10
  subsumption eq53 eq35


@[equational_result]
theorem Equation885_implies_Equation938 (G : Type*) [Magma G] (h : Equation885 G) : Equation938 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X2 ◇ X0))) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq26 (X0 : G) : sK0 ≠ (X0 ◇ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq26 eq24


@[equational_result]
theorem Equation886_implies_Equation3177 (G : Type*) [Magma G] (h : Equation886 G) : Equation3177 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK2) ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1)))) = ((X1 ◇ (X4 ◇ (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1)))))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X5 ◇ (X1 ◇ (X4 ◇ (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))))))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq18 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq28 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1))) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq30 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X3 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq33 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X0) = ((X3 ◇ (X4 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X5 ◇ (X3 ◇ (X4 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X0)))))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.1 in 11
  have eq36 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2) = X1 := superpose eq31 eq18 -- backward demodulation 18,31
  have eq38 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X0) ◇ X0)))) = X0 := superpose eq31 eq11 -- backward demodulation 11,31
  have eq41 (X0 X1 X3 X4 X5 : G) : (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X1))) = ((X1 ◇ (X4 ◇ (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X1))))) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X5 ◇ (X1 ◇ (X4 ◇ (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X1)))))))) := superpose eq31 eq14 -- backward demodulation 14,31
  have eq51 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq30 eq41 -- forward demodulation 41,30
  have eq53 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq51 eq38 -- backward demodulation 38,51
  have eq58 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X0) = ((X3 ◇ (X4 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1))) := superpose eq31 eq33 -- forward demodulation 33,31
  have eq59 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = ((X3 ◇ (X4 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))) := superpose eq31 eq58 -- forward demodulation 58,31
  have eq60 (X0 X1 X3 X4 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = ((X3 ◇ (X4 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq31 eq59 -- forward demodulation 59,31
  have eq72 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq53 eq31 -- superposition 31,53, 53 into 31, unify on (0).2 in 53 and (0).2 in 31
  have eq84 (X0 X1 X3 X4 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = ((X3 ◇ (X4 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0))) ◇ X1) := superpose eq72 eq60 -- backward demodulation 60,72
  have eq85 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq72 eq36 -- backward demodulation 36,72
  have eq87 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X1))) = X3 := superpose eq85 eq28 -- backward demodulation 28,85
  have eq108 (X0 X1 X3 X4 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X0) = ((X3 ◇ (X4 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X0))) ◇ X1) := superpose eq85 eq84 -- backward demodulation 84,85
  have eq109 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ sK1) := superpose eq85 eq10 -- backward demodulation 10,85
  have eq112 (X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = X3 := superpose eq85 eq87 -- forward demodulation 87,85
  have eq113 (X2 X3 : G) : (X2 ◇ X3) = X3 := superpose eq85 eq112 -- forward demodulation 112,85
  have eq144 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose eq113 eq108 -- forward demodulation 108,113
  have eq145 (X0 X1 X3 : G) : (X3 ◇ X0) = X1 := superpose eq85 eq144 -- forward demodulation 144,85
  subsumption eq109 eq145


@[equational_result]
theorem Equation889_implies_Equation1613 (G : Type*) [Magma G] (h : Equation889 G) : Equation1613 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK0))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq11


@[equational_result]
theorem Equation890_implies_Equation745 (G : Type*) [Magma G] (h : Equation890 G) : Equation745 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK0 ◇ sK1) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = X1 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq35 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK2)) := superpose eq28 eq10 -- backward demodulation 10,28
  have eq42 (X2 X3 : G) : X2 = X3 := superpose eq17 eq17 -- superposition 17,17, 17 into 17, unify on (0).2 in 17 and (0).1 in 17
  have eq103 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq35 -- superposition 35,42, 42 into 35, unify on (0).2 in 42 and (0).2 in 35
  subsumption eq103 eq42


@[equational_result]
theorem Equation893_implies_Equation955 (G : Type*) [Magma G] (h : Equation893 G) : Equation955 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq37 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1 in 16
  have eq53 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK3 ◇ sK0))) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2 in 10
  subsumption eq53 eq37


@[equational_result]
theorem Equation895_implies_Equation1571 (G : Type*) [Magma G] (h : Equation895 G) : Equation1571 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.2 in 12
  have eq28 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2.2 in 11
  have eq29 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq38 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.2 in 9
  have eq58 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X2) = X3 := superpose eq17 eq29 -- superposition 29,17, 17 into 29, unify on (0).2 in 17 and (0).1.1.2.1 in 29
  have eq73 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) = X3 := superpose eq17 eq29 -- superposition 29,17, 17 into 29, unify on (0).2 in 17 and (0).1 in 29
  have eq83 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) := superpose eq29 eq9 -- superposition 9,29, 29 into 9, unify on (0).2 in 29 and (0).1.2 in 9
  have eq84 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X4) ◇ ((X5 ◇ X3) ◇ X4))) = (X2 ◇ (X5 ◇ X0)) := superpose eq29 eq12 -- superposition 12,29, 29 into 12, unify on (0).2 in 29 and (0).1.2.1 in 12
  have eq87 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2) = X3 := superpose eq17 eq58 -- forward demodulation 58,17
  have eq88 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X3 := superpose eq38 eq87 -- forward demodulation 87,38
  have eq92 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq83 eq26 -- backward demodulation 26,83
  have eq93 (X0 X2 X4 : G) : (X4 ◇ (X0 ◇ (X4 ◇ X2))) = (X2 ◇ X0) := superpose eq83 eq28 -- backward demodulation 28,83
  have eq105 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq92 eq73 -- backward demodulation 73,92
  have eq114 (X0 X1 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X5) := superpose eq92 eq84 -- forward demodulation 84,92
  have eq188 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X1 ◇ X0) := superpose eq9 eq88 -- superposition 88,9, 9 into 88, unify on (0).2 in 9 and (0).1.1 in 88
  have eq233 (X0 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = ((X0 ◇ X2) ◇ X5) := superpose eq188 eq114 -- backward demodulation 114,188
  have eq259 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ (X2 ◇ (X0 ◇ X4))) = X4 := superpose eq233 eq92 -- backward demodulation 92,233
  have eq399 (X0 X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq93 eq105 -- superposition 105,93, 93 into 105, unify on (0).2 in 93 and (0).1 in 105
  have eq408 (X0 X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq233 eq399 -- forward demodulation 399,233
  have eq409 (X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ X1) := superpose eq38 eq408 -- forward demodulation 408,38
  have eq437 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := superpose eq259 eq88 -- superposition 88,259, 259 into 88, unify on (0).2 in 259 and (0).1.1 in 88
  have eq461 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK1))) := superpose eq437 eq10 -- backward demodulation 10,437
  have eq462 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := superpose eq409 eq461 -- forward demodulation 461,409
  subsumption eq462 eq38


@[equational_result]
theorem Equation895_implies_Equation2282 (G : Type*) [Magma G] (h : Equation895 G) : Equation2282 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq20 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq22 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1.2.2 in 11
  have eq52 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2.2 in 11
  have eq53 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq56 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq22 eq22 -- superposition 22,22, 22 into 22, unify on (0).2 in 22 and (0).1.2 in 22
  have eq69 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3)) = X2 := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.2.1.2.2 in 12
  have eq93 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq22 eq53 -- superposition 53,22, 22 into 53, unify on (0).2 in 22 and (0).1.1 in 53
  have eq108 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X4) ◇ ((X5 ◇ X3) ◇ X4))) = (X2 ◇ (X5 ◇ X0)) := superpose eq53 eq12 -- superposition 12,53, 53 into 12, unify on (0).2 in 53 and (0).1.2.1 in 12
  have eq122 (X0 X2 X4 : G) : (X2 ◇ X0) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq93 eq52 -- backward demodulation 52,93
  have eq142 (X0 X1 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X5) := superpose eq93 eq108 -- forward demodulation 108,93
  have eq148 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X1 ◇ X0) := superpose eq9 eq56 -- superposition 56,9, 9 into 56, unify on (0).2 in 9 and (0).1.1 in 56
  have eq197 (X0 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = ((X0 ◇ X2) ◇ X5) := superpose eq148 eq142 -- backward demodulation 142,148
  have eq222 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X3 ◇ X2))) = X2 := superpose eq197 eq69 -- backward demodulation 69,197
  have eq232 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X3 ◇ X2) ◇ (X3 ◇ (X1 ◇ X0))))) = X2 := superpose eq197 eq222 -- forward demodulation 222,197
  have eq233 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)))) = X2 := superpose eq197 eq232 -- forward demodulation 232,197
  have eq234 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq56 eq233 -- forward demodulation 233,56
  have eq235 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq122 eq234 -- forward demodulation 234,122
  have eq348 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq197 eq20 -- superposition 20,197, 197 into 20, unify on (0).2 in 197 and (0).2 in 20
  subsumption eq348 eq235


@[equational_result]
theorem Equation895_implies_Equation2402 (G : Type*) [Magma G] (h : Equation895 G) : Equation2402 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.2 in 12
  have eq33 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2.2 in 11
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq36 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1 in 12
  have eq58 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X2) = X3 := superpose eq17 eq34 -- superposition 34,17, 17 into 34, unify on (0).2 in 17 and (0).1.1.2.1 in 34
  have eq73 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) = X3 := superpose eq17 eq34 -- superposition 34,17, 17 into 34, unify on (0).2 in 17 and (0).1 in 34
  have eq77 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) := superpose eq34 eq9 -- superposition 9,34, 34 into 9, unify on (0).2 in 34 and (0).1.2 in 9
  have eq84 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X4) ◇ ((X5 ◇ X3) ◇ X4))) = (X2 ◇ (X5 ◇ X0)) := superpose eq34 eq12 -- superposition 12,34, 34 into 12, unify on (0).2 in 34 and (0).1.2.1 in 12
  have eq87 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2) = X3 := superpose eq17 eq58 -- forward demodulation 58,17
  have eq88 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X3 := superpose eq36 eq87 -- forward demodulation 87,36
  have eq92 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq77 eq26 -- backward demodulation 26,77
  have eq93 (X0 X2 X4 : G) : (X4 ◇ (X0 ◇ (X4 ◇ X2))) = (X2 ◇ X0) := superpose eq77 eq33 -- backward demodulation 33,77
  have eq101 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq92 eq73 -- backward demodulation 73,92
  have eq116 (X0 X1 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X5) := superpose eq92 eq84 -- forward demodulation 84,92
  have eq134 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3)) = X2 := superpose eq36 eq12 -- superposition 12,36, 36 into 12, unify on (0).2 in 36 and (0).1.2.1.2.2 in 12
  have eq190 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X1 ◇ X0) := superpose eq9 eq88 -- superposition 88,9, 9 into 88, unify on (0).2 in 9 and (0).1.1 in 88
  have eq235 (X0 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = ((X0 ◇ X2) ◇ X5) := superpose eq190 eq116 -- backward demodulation 116,190
  have eq258 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X3 ◇ X2))) = X2 := superpose eq235 eq134 -- backward demodulation 134,235
  have eq286 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X3 ◇ X2) ◇ (X3 ◇ (X1 ◇ X0))))) = X2 := superpose eq235 eq258 -- forward demodulation 258,235
  have eq287 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)))) = X2 := superpose eq235 eq286 -- forward demodulation 286,235
  have eq288 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq88 eq287 -- forward demodulation 287,88
  have eq289 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq93 eq288 -- forward demodulation 288,93
  have eq291 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq289 eq10 -- backward demodulation 10,289
  subsumption eq291 eq101


