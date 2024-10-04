import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation1636_implies_Equation1849 (G : Type*) [Magma G] (h : Equation1636 G) : Equation1849 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X3) ◇ (X0 ◇ X3)) ◇ (((X1 ◇ X0) ◇ X2) ◇ X4)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq74 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2.1 in 15
  have eq341 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq16 eq74 -- superposition 74,16, 16 into 74, unify on (0).2 in 16 and (0).2.2 in 74
  have eq377 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := superpose eq341 eq10 -- backward demodulation 10,341
  subsumption eq377 eq14


@[equational_result]
theorem Equation3097_implies_Equation307 (G : Type*) [Magma G] (h : Equation3097 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq15 rfl


@[equational_result]
theorem Equation1024_implies_Equation3457 (G : Type*) [Magma G] (h : Equation1024 G) : Equation3457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq14 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq18 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2.1 in 9
  have eq22 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq18 eq12 -- backward demodulation 12,18
  have eq27 : sK0 ≠ sK0 := superpose eq22 eq13 -- superposition 13,22, 22 into 13, unify on (0).2 in 22 and (0).2 in 13
  subsumption eq27 rfl


@[equational_result]
theorem Equation1024_implies_Equation424 (G : Type*) [Magma G] (h : Equation1024 G) : Equation424 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq26 (X0 X3 : G) : (X0 ◇ (X0 ◇ X3)) = X0 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq27 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq27 eq26


@[equational_result]
theorem Equation1024_implies_Equation416 (G : Type*) [Magma G] (h : Equation1024 G) : Equation416 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq26 (X0 X3 : G) : (X0 ◇ (X0 ◇ X3)) = X0 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq27 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq27 eq26


@[equational_result]
theorem Equation2804_implies_Equation3522 (G : Type*) [Magma G] (h : Equation2804 G) : Equation3522 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq17 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq19 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq18 -- forward demodulation 18,17
  subsumption eq19 rfl


@[equational_result]
theorem Equation2804_implies_Equation3659 (G : Type*) [Magma G] (h : Equation2804 G) : Equation3659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq12 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) = X2 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq16 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq8 eq12 -- forward demodulation 12,8
  have eq17 : sK0 ≠ (sK0 ◇ sK0) := superpose eq16 eq9 -- backward demodulation 9,16
  subsumption eq17 eq16


@[equational_result]
theorem Equation2804_implies_Equation3253 (G : Type*) [Magma G] (h : Equation2804 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq12 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) = X2 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq16 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq8 eq12 -- forward demodulation 12,8
  have eq17 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq16 eq9 -- backward demodulation 9,16
  have eq18 : sK0 ≠ (sK0 ◇ sK0) := superpose eq16 eq17 -- forward demodulation 17,16
  subsumption eq18 eq16


@[equational_result]
theorem Equation2804_implies_Equation2087 (G : Type*) [Magma G] (h : Equation2804 G) : Equation2087 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq17 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq18 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq21 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.1.2 in 9
  have eq60 : sK0 ≠ sK0 := superpose eq21 eq18 -- superposition 18,21, 21 into 18, unify on (0).2 in 21 and (0).2 in 18
  subsumption eq60 rfl


@[equational_result]
theorem Equation2804_implies_Equation1629 (G : Type*) [Magma G] (h : Equation2804 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq12 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) = X2 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq16 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq8 eq12 -- forward demodulation 12,8
  have eq17 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq16 eq9 -- backward demodulation 9,16
  have eq18 : sK0 ≠ (sK0 ◇ sK0) := superpose eq16 eq17 -- forward demodulation 17,16
  subsumption eq18 eq16


@[equational_result]
theorem Equation2804_implies_Equation228 (G : Type*) [Magma G] (h : Equation2804 G) : Equation228 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2804_implies_Equation4118 (G : Type*) [Magma G] (h : Equation2804 G) : Equation4118 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq17 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq18 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq19 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq18 -- forward demodulation 18,17
  subsumption eq19 rfl


@[equational_result]
theorem Equation2804_implies_Equation270 (G : Type*) [Magma G] (h : Equation2804 G) : Equation270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq17 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq38 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.1.2 in 9
  have eq89 : sK0 ≠ sK0 := superpose eq38 eq10 -- superposition 10,38, 38 into 10, unify on (0).2 in 38 and (0).2 in 10
  subsumption eq89 rfl


@[equational_result]
theorem Equation2804_implies_Equation3915 (G : Type*) [Magma G] (h : Equation2804 G) : Equation3915 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq17 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq18 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq19 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq18 -- forward demodulation 18,17
  subsumption eq19 rfl


@[equational_result]
theorem Equation3908_implies_Equation4099 (G : Type*) [Magma G] (h : Equation3908 G) : Equation4099 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq16 (X3 X4 X5 : G) : (X4 ◇ X4) = ((X3 ◇ X3) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq62 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK3) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1 in 10
  subsumption eq62 eq16


@[equational_result]
theorem Equation775_implies_Equation1289 (G : Type*) [Magma G] (h : Equation775 G) : Equation1289 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = (X3 ◇ (X0 ◇ (X2 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq23 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1))) := superpose eq18 eq10 -- backward demodulation 10,18
  have eq24 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := superpose eq18 eq23 -- forward demodulation 23,18
  have eq116 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ ((X0 ◇ sK0) ◇ sK1))) := superpose eq11 eq24 -- superposition 24,11, 11 into 24, unify on (0).2 in 11 and (0).2.2 in 24
  subsumption eq116 eq9


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
theorem Equation3487_implies_Equation3664 (G : Type*) [Magma G] (h : Equation3487 G) : Equation3664 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq25 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X2)) = (((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.2 in 13
  have eq34 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X2 ◇ X2)) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq92 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq34 eq10 -- superposition 10,34, 34 into 10, unify on (0).2 in 34 and (0).2 in 10
  subsumption eq92 rfl


@[equational_result]
theorem Equation3487_implies_Equation3499 (G : Type*) [Magma G] (h : Equation3487 G) : Equation3499 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq34 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq34 rfl


@[equational_result]
theorem Equation2573_implies_Equation1038 (G : Type*) [Magma G] (h : Equation2573 G) : Equation1038 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ ((X3 ◇ X1) ◇ X2)) ◇ X3) ◇ (X4 ◇ ((X5 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X4))) = X5 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq22 (X0 X1 X4 X5 : G) : (X1 ◇ (X4 ◇ ((X5 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X4))) = X5 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq29 (X0 X1 X3 X4 : G) : (X0 ◇ (X1 ◇ X0)) = ((X3 ◇ X1) ◇ (X4 ◇ (X3 ◇ X4))) := superpose eq11 eq22 -- superposition 22,11, 11 into 22, unify on (0).2 in 11 and (0).1.2.2.1 in 22
  have eq54 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X4)) = ((X3 ◇ (X1 ◇ X3)) ◇ (X5 ◇ ((X0 ◇ X1) ◇ X5))) := superpose eq29 eq29 -- superposition 29,29, 29 into 29, unify on (0).2 in 29 and (0).2.1 in 29
  have eq99 (X0 X2 X4 : G) : (X4 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X4)) = X0 := superpose eq11 eq54 -- forward demodulation 54,11
  have eq202 : sK0 ≠ sK0 := superpose eq99 eq10 -- superposition 10,99, 99 into 10, unify on (0).2 in 99 and (0).2 in 10
  subsumption eq202 rfl


@[equational_result]
theorem Equation2573_implies_Equation1155 (G : Type*) [Magma G] (h : Equation2573 G) : Equation1155 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ ((X3 ◇ X1) ◇ X2)) ◇ X3) ◇ (X4 ◇ ((X5 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X4))) = X5 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq22 (X0 X1 X4 X5 : G) : (X1 ◇ (X4 ◇ ((X5 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X4))) = X5 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq29 (X0 X1 X3 X4 : G) : (X0 ◇ (X1 ◇ X0)) = ((X3 ◇ X1) ◇ (X4 ◇ (X3 ◇ X4))) := superpose eq11 eq22 -- superposition 22,11, 11 into 22, unify on (0).2 in 11 and (0).1.2.2.1 in 22
  have eq54 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X4)) = ((X3 ◇ (X1 ◇ X3)) ◇ (X5 ◇ ((X0 ◇ X1) ◇ X5))) := superpose eq29 eq29 -- superposition 29,29, 29 into 29, unify on (0).2 in 29 and (0).2.1 in 29
  have eq99 (X0 X2 X4 : G) : (X4 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X4)) = X0 := superpose eq11 eq54 -- forward demodulation 54,11
  have eq202 : sK0 ≠ sK0 := superpose eq99 eq10 -- superposition 10,99, 99 into 10, unify on (0).2 in 99 and (0).2 in 10
  subsumption eq202 rfl


@[equational_result]
theorem Equation2066_implies_Equation3316 (G : Type*) [Magma G] (h : Equation2066 G) : Equation3316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X0) = ((((X2 ◇ X0) ◇ X3) ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.1.1 in 13
  have eq140 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq207 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq140 eq9 -- superposition 9,140, 140 into 9, unify on (0).2 in 140 and (0).1.1 in 9
  have eq296 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq207 eq10 -- superposition 10,207, 207 into 10, unify on (0).2 in 207 and (0).2 in 10
  subsumption eq296 rfl


@[equational_result]
theorem Equation2066_implies_Equation3258 (G : Type*) [Magma G] (h : Equation2066 G) : Equation3258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X0) = ((((X2 ◇ X0) ◇ X3) ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.1.1 in 13
  have eq140 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq207 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq140 eq9 -- superposition 9,140, 140 into 9, unify on (0).2 in 140 and (0).1.1 in 9
  have eq296 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq207 eq10 -- superposition 10,207, 207 into 10, unify on (0).2 in 207 and (0).2 in 10
  subsumption eq296 rfl


@[equational_result]
theorem Equation2066_implies_Equation3306 (G : Type*) [Magma G] (h : Equation2066 G) : Equation3306 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X0) = ((((X2 ◇ X0) ◇ X3) ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.1.1 in 13
  have eq140 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq207 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq140 eq9 -- superposition 9,140, 140 into 9, unify on (0).2 in 140 and (0).1.1 in 9
  have eq278 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq207 eq10 -- superposition 10,207, 207 into 10, unify on (0).2 in 207 and (0).2 in 10
  subsumption eq278 rfl


@[equational_result]
theorem Equation2066_implies_Equation3326 (G : Type*) [Magma G] (h : Equation2066 G) : Equation3326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X0) = ((((X2 ◇ X0) ◇ X3) ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.1.1 in 13
  have eq140 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq207 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq140 eq9 -- superposition 9,140, 140 into 9, unify on (0).2 in 140 and (0).1.1 in 9
  have eq296 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq207 eq10 -- superposition 10,207, 207 into 10, unify on (0).2 in 207 and (0).2 in 10
  subsumption eq296 rfl


@[equational_result]
theorem Equation2683_implies_Equation263 (G : Type*) [Magma G] (h : Equation2683 G) : Equation263 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X3 : G) : (((X3 ◇ X0) ◇ X0) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation2683_implies_Equation3253 (G : Type*) [Magma G] (h : Equation2683 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (((X3 ◇ X0) ◇ X0) ◇ X3) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq16 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq20 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq16 eq9 -- backward demodulation 9,16
  subsumption eq20 eq16


@[equational_result]
theorem Equation624_implies_Equation47 (G : Type*) [Magma G] (h : Equation624 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X0))) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq14 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq14 rfl


@[equational_result]
theorem Equation624_implies_Equation50 (G : Type*) [Magma G] (h : Equation624 G) : Equation50 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation916_implies_Equation1426 (G : Type*) [Magma G] (h : Equation916 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.2 in 10
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2.2 in 8
  have eq18 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq8 eq13 -- superposition 13,8, 8 into 13, unify on (0).2 in 8 and (0).2.2 in 13
  have eq20 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq18 -- forward demodulation 18,8
  have eq21 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq20 -- forward demodulation 20,10
  have eq22 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq21 eq11 -- backward demodulation 11,21
  have eq26 : sK0 ≠ sK0 := superpose eq22 eq9 -- superposition 9,22, 22 into 9, unify on (0).2 in 22 and (0).2 in 9
  subsumption eq26 rfl


@[equational_result]
theorem Equation916_implies_Equation359 (G : Type*) [Magma G] (h : Equation916 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq11 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2 in 8
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2.2 in 8
  have eq15 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq10 eq12 -- superposition 12,10, 10 into 12, unify on (0).2 in 10 and (0).1.2.2 in 12
  have eq18 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq8 eq13 -- superposition 13,8, 8 into 13, unify on (0).2 in 8 and (0).2.2 in 13
  have eq20 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq18 -- forward demodulation 18,8
  have eq21 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq20 -- forward demodulation 20,10
  have eq22 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq21 eq11 -- backward demodulation 11,21
  have eq24 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq28 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq24 eq9 -- superposition 9,24, 24 into 9, unify on (0).2 in 24 and (0).2 in 9
  subsumption eq28 rfl


@[equational_result]
theorem Equation916_implies_Equation614 (G : Type*) [Magma G] (h : Equation916 G) : Equation614 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq11 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2 in 8
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2.2 in 8
  have eq17 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq10 eq13 -- superposition 13,10, 10 into 13, unify on (0).2 in 10 and (0).1 in 13
  have eq18 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq8 eq13 -- superposition 13,8, 8 into 13, unify on (0).2 in 8 and (0).2.2 in 13
  have eq20 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq18 -- forward demodulation 18,8
  have eq21 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq20 -- forward demodulation 20,10
  have eq22 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq21 eq11 -- backward demodulation 11,21
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq22 eq17 -- backward demodulation 17,22
  have eq25 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq23 eq9 -- backward demodulation 9,23
  subsumption eq25 eq12


@[equational_result]
theorem Equation916_implies_Equation4065 (G : Type*) [Magma G] (h : Equation916 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq11 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2 in 8
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2.2 in 8
  have eq15 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq10 eq12 -- superposition 12,10, 10 into 12, unify on (0).2 in 10 and (0).1.2.2 in 12
  have eq18 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq8 eq13 -- superposition 13,8, 8 into 13, unify on (0).2 in 8 and (0).2.2 in 13
  have eq20 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq18 -- forward demodulation 18,8
  have eq21 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq20 -- forward demodulation 20,10
  have eq22 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq21 eq11 -- backward demodulation 11,21
  have eq24 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq25 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq24 eq9 -- backward demodulation 9,24
  subsumption eq25 eq24


@[equational_result]
theorem Equation916_implies_Equation642 (G : Type*) [Magma G] (h : Equation916 G) : Equation642 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq13 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.2 in 9
  have eq18 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq11 eq14 -- superposition 14,11, 11 into 14, unify on (0).2 in 11 and (0).1 in 14
  have eq19 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.2 in 14
  have eq21 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq19 -- forward demodulation 19,9
  have eq22 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq21 -- forward demodulation 21,11
  have eq23 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq22 eq12 -- backward demodulation 12,22
  have eq24 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq23 eq18 -- backward demodulation 18,23
  have eq26 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq24 eq10 -- backward demodulation 10,24
  subsumption eq26 eq13


@[equational_result]
theorem Equation916_implies_Equation3862 (G : Type*) [Magma G] (h : Equation916 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq11 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.2 in 10
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2.2 in 8
  have eq18 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq8 eq13 -- superposition 13,8, 8 into 13, unify on (0).2 in 8 and (0).2.2 in 13
  have eq20 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq18 -- forward demodulation 18,8
  have eq21 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq20 -- forward demodulation 20,10
  have eq22 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq21 eq11 -- backward demodulation 11,21
  have eq25 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq10 eq22 -- superposition 22,10, 10 into 22, unify on (0).2 in 10 and (0).1.1 in 22
  have eq26 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq22 eq25 -- forward demodulation 25,22
  have eq40 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).2 in 9
  subsumption eq40 rfl


@[equational_result]
theorem Equation916_implies_Equation47 (G : Type*) [Magma G] (h : Equation916 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2 in 8
  have eq16 : sK0 ≠ sK0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq16 rfl


@[equational_result]
theorem Equation415_implies_Equation3862 (G : Type*) [Magma G] (h : Equation415 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq13 rfl


@[equational_result]
theorem Equation415_implies_Equation375 (G : Type*) [Magma G] (h : Equation415 G) : Equation375 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 rfl


@[equational_result]
theorem Equation415_implies_Equation817 (G : Type*) [Magma G] (h : Equation415 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq14 -- forward demodulation 14,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation415_implies_Equation4470 (G : Type*) [Magma G] (h : Equation415 G) : Equation4470 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq15 -- forward demodulation 15,13
  subsumption eq16 rfl


@[equational_result]
theorem Equation415_implies_Equation3659 (G : Type*) [Magma G] (h : Equation415 G) : Equation3659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq9 -- backward demodulation 9,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation415_implies_Equation615 (G : Type*) [Magma G] (h : Equation415 G) : Equation615 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X3 ◇ (X3 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq11


@[equational_result]
theorem Equation415_implies_Equation4118 (G : Type*) [Magma G] (h : Equation415 G) : Equation4118 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq15 -- forward demodulation 15,13
  subsumption eq16 rfl


@[equational_result]
theorem Equation415_implies_Equation326 (G : Type*) [Magma G] (h : Equation415 G) : Equation326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 rfl


@[equational_result]
theorem Equation415_implies_Equation3522 (G : Type*) [Magma G] (h : Equation415 G) : Equation3522 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq15 -- forward demodulation 15,13
  subsumption eq16 rfl


@[equational_result]
theorem Equation415_implies_Equation48 (G : Type*) [Magma G] (h : Equation415 G) : Equation48 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X3 ◇ (X3 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq23 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq23 rfl


@[equational_result]
theorem Equation2860_implies_Equation2062 (G : Type*) [Magma G] (h : Equation2860 G) : Equation2062 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq42 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X3) ◇ X3) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq52 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.1 in 9
  have eq93 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2)) := superpose eq52 eq12 -- superposition 12,52, 52 into 12, unify on (0).2 in 52 and (0).1.2 in 12
  have eq102 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X2)) = X0 := superpose eq52 eq93 -- forward demodulation 93,52
  have eq376 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ X0) ◇ (sK0 ◇ sK2)) := superpose eq42 eq10 -- superposition 10,42, 42 into 10, unify on (0).2 in 42 and (0).2.1 in 10
  subsumption eq376 eq102


@[equational_result]
theorem Equation2860_implies_Equation2660 (G : Type*) [Magma G] (h : Equation2860 G) : Equation2660 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq17 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq19 (X0 X1 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3)) = X0 := superpose eq15 eq17 -- forward demodulation 17,15
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq30 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3)) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.2 in 12
  have eq42 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X3) ◇ X3) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq48 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq26 eq12 -- superposition 12,26, 26 into 12, unify on (0).2 in 26 and (0).2.2 in 12
  have eq49 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.1 in 9
  have eq52 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X3) ◇ X3) := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.1.1.2 in 9
  have eq54 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq26 eq12 -- superposition 12,26, 26 into 12, unify on (0).2 in 26 and (0).2.2 in 12
  have eq86 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq49 eq49 -- superposition 49,49, 49 into 49, unify on (0).2 in 49 and (0).1.1 in 49
  have eq144 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0))) := superpose eq86 eq11 -- superposition 11,86, 86 into 11, unify on (0).2 in 86 and (0).2.1 in 11
  have eq149 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq86 eq12 -- superposition 12,86, 86 into 12, unify on (0).2 in 86 and (0).1 in 12
  have eq150 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq86 eq9 -- superposition 9,86, 86 into 9, unify on (0).2 in 86 and (0).1.1.1 in 9
  have eq175 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq26 eq15 -- superposition 15,26, 26 into 15, unify on (0).2 in 26 and (0).1.2 in 15
  have eq207 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X2) ◇ X2) ◇ X3) ◇ X3) := superpose eq175 eq52 -- backward demodulation 52,175
  have eq234 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) := superpose eq150 eq19 -- superposition 19,150, 150 into 19, unify on (0).2 in 150 and (0).1.1.1.2 in 19
  have eq235 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq150 eq26 -- superposition 26,150, 150 into 26, unify on (0).2 in 150 and (0).1.1.2 in 26
  have eq309 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq150 eq42 -- superposition 42,150, 150 into 42, unify on (0).2 in 150 and (0).1.1 in 42
  have eq402 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq309 eq235 -- backward demodulation 235,309
  have eq404 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq402 eq234 -- backward demodulation 234,402
  have eq407 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq404 eq15 -- backward demodulation 15,404
  have eq412 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) := superpose eq407 eq54 -- backward demodulation 54,407
  have eq432 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq149 eq412 -- forward demodulation 412,149
  have eq440 (X0 X2 X3 : G) : ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ X3)) = ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq432 eq30 -- backward demodulation 30,432
  have eq447 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq432 eq48 -- backward demodulation 48,432
  have eq457 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = (((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ (((X0 ◇ X0) ◇ X2) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ (((X0 ◇ X0) ◇ X2) ◇ X0))) := superpose eq432 eq144 -- backward demodulation 144,432
  have eq465 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq432 eq407 -- backward demodulation 407,432
  have eq467 (X0 X2 X3 : G) : (X0 ◇ X2) = ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ X3)) := superpose eq402 eq440 -- forward demodulation 440,402
  have eq598 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq49 eq432 -- superposition 432,49, 49 into 432, unify on (0).2 in 49 and (0).1.2 in 432
  have eq610 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq49 eq598 -- forward demodulation 598,49
  have eq631 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) := superpose eq86 eq467 -- superposition 467,86, 86 into 467, unify on (0).2 in 86 and (0).2 in 467
  have eq650 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq631 eq457 -- backward demodulation 457,631
  have eq684 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) := superpose eq42 eq447 -- superposition 447,42, 42 into 447, unify on (0).2 in 42 and (0).2.2.1 in 447
  have eq706 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) := superpose eq650 eq684 -- forward demodulation 684,650
  have eq1368 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (X0 ◇ (X0 ◇ X3))) := superpose eq207 eq465 -- superposition 465,207, 207 into 465, unify on (0).2 in 207 and (0).2.2 in 465
  have eq1479 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq432 eq1368 -- forward demodulation 1368,432
  have eq1480 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = (((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ (X0 ◇ X0)) := superpose eq650 eq1479 -- forward demodulation 1479,650
  have eq1481 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = ((X0 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq610 eq1480 -- forward demodulation 1480,610
  have eq1482 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq706 eq1481 -- forward demodulation 1481,706
  have eq1483 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq1482 eq10 -- backward demodulation 10,1482
  subsumption eq1483 eq150


@[equational_result]
theorem Equation2860_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2860 G) : Equation2644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ X3) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.2 in 8
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2.2 in 11
  have eq16 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3)) = X0 := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1 in 8
  have eq18 (X0 X1 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3)) = X0 := superpose eq14 eq16 -- forward demodulation 16,14
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X2) ◇ X2) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1.1 in 10
  have eq41 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X3) ◇ X3) := superpose eq25 eq25 -- superposition 25,25, 25 into 25, unify on (0).2 in 25 and (0).1 in 25
  have eq48 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq25 eq8 -- superposition 8,25, 25 into 8, unify on (0).2 in 25 and (0).1.1 in 8
  have eq53 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq25 eq11 -- superposition 11,25, 25 into 11, unify on (0).2 in 25 and (0).2.2 in 11
  have eq85 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq48 eq48 -- superposition 48,48, 48 into 48, unify on (0).2 in 48 and (0).1.1 in 48
  have eq148 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq85 eq11 -- superposition 11,85, 85 into 11, unify on (0).2 in 85 and (0).1 in 11
  have eq149 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq85 eq8 -- superposition 8,85, 85 into 8, unify on (0).2 in 85 and (0).1.1.1 in 8
  have eq155 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq85 eq25 -- superposition 25,85, 85 into 25, unify on (0).2 in 85 and (0).2.1 in 25
  have eq233 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) := superpose eq149 eq18 -- superposition 18,149, 149 into 18, unify on (0).2 in 149 and (0).1.1.1.2 in 18
  have eq234 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq149 eq25 -- superposition 25,149, 149 into 25, unify on (0).2 in 149 and (0).1.1.2 in 25
  have eq308 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq149 eq41 -- superposition 41,149, 149 into 41, unify on (0).2 in 149 and (0).1.1 in 41
  have eq401 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq308 eq234 -- backward demodulation 234,308
  have eq403 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq401 eq233 -- backward demodulation 233,401
  have eq406 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq403 eq14 -- backward demodulation 14,403
  have eq411 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) := superpose eq406 eq53 -- backward demodulation 53,406
  have eq431 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq148 eq411 -- forward demodulation 411,148
  have eq457 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq431 eq155 -- backward demodulation 155,431
  have eq473 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq457 eq9 -- backward demodulation 9,457
  subsumption eq473 eq48


@[equational_result]
theorem Equation2860_implies_Equation3257 (G : Type*) [Magma G] (h : Equation2860 G) : Equation3257 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq18 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq19 (X0 X1 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3)) = X0 := superpose eq15 eq18 -- forward demodulation 18,15
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq42 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X3) ◇ X3) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq49 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.1 in 9
  have eq54 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq26 eq12 -- superposition 12,26, 26 into 12, unify on (0).2 in 26 and (0).2.2 in 12
  have eq86 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq49 eq49 -- superposition 49,49, 49 into 49, unify on (0).2 in 49 and (0).1.1 in 49
  have eq143 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq86 eq12 -- superposition 12,86, 86 into 12, unify on (0).2 in 86 and (0).1 in 12
  have eq144 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq86 eq9 -- superposition 9,86, 86 into 9, unify on (0).2 in 86 and (0).1.1.1 in 9
  have eq234 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) := superpose eq144 eq19 -- superposition 19,144, 144 into 19, unify on (0).2 in 144 and (0).1.1.1.2 in 19
  have eq235 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq144 eq26 -- superposition 26,144, 144 into 26, unify on (0).2 in 144 and (0).1.1.2 in 26
  have eq309 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq144 eq42 -- superposition 42,144, 144 into 42, unify on (0).2 in 144 and (0).1.1 in 42
  have eq402 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq309 eq235 -- backward demodulation 235,309
  have eq404 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq402 eq234 -- backward demodulation 234,402
  have eq407 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq404 eq15 -- backward demodulation 15,404
  have eq412 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) := superpose eq407 eq54 -- backward demodulation 54,407
  have eq432 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq143 eq412 -- forward demodulation 412,143
  have eq610 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq432 eq10 -- superposition 10,432, 432 into 10, unify on (0).2 in 432 and (0).2 in 10
  subsumption eq610 rfl


@[equational_result]
theorem Equation2860_implies_Equation3458 (G : Type*) [Magma G] (h : Equation2860 G) : Equation3458 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq17 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq19 (X0 X1 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3)) = X0 := superpose eq15 eq17 -- forward demodulation 17,15
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq42 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X3) ◇ X3) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq49 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.1 in 9
  have eq54 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq26 eq12 -- superposition 12,26, 26 into 12, unify on (0).2 in 26 and (0).2.2 in 12
  have eq86 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq49 eq49 -- superposition 49,49, 49 into 49, unify on (0).2 in 49 and (0).1.1 in 49
  have eq149 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq86 eq12 -- superposition 12,86, 86 into 12, unify on (0).2 in 86 and (0).1 in 12
  have eq150 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq86 eq9 -- superposition 9,86, 86 into 9, unify on (0).2 in 86 and (0).1.1.1 in 9
  have eq234 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) := superpose eq150 eq19 -- superposition 19,150, 150 into 19, unify on (0).2 in 150 and (0).1.1.1.2 in 19
  have eq235 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq150 eq26 -- superposition 26,150, 150 into 26, unify on (0).2 in 150 and (0).1.1.2 in 26
  have eq309 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq150 eq42 -- superposition 42,150, 150 into 42, unify on (0).2 in 150 and (0).1.1 in 42
  have eq365 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) ◇ X3) ◇ X0) := superpose eq42 eq11 -- superposition 11,42, 42 into 11, unify on (0).2 in 42 and (0).2.1 in 11
  have eq402 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq309 eq235 -- backward demodulation 235,309
  have eq404 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq402 eq234 -- backward demodulation 234,402
  have eq407 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq404 eq15 -- backward demodulation 15,404
  have eq412 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) := superpose eq407 eq54 -- backward demodulation 54,407
  have eq432 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq149 eq412 -- forward demodulation 412,149
  have eq557 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X2) = (((((X0 ◇ X0) ◇ X2) ◇ X3) ◇ X3) ◇ X0) := superpose eq432 eq365 -- forward demodulation 365,432
  have eq558 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X2) ◇ X0) := superpose eq309 eq557 -- forward demodulation 557,309
  have eq559 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := superpose eq558 eq10 -- backward demodulation 10,558
  subsumption eq559 eq149


@[equational_result]
theorem Equation2860_implies_Equation261 (G : Type*) [Magma G] (h : Equation2860 G) : Equation261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq17 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq19 (X0 X1 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3)) = X0 := superpose eq15 eq17 -- forward demodulation 17,15
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq42 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X3) ◇ X3) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq49 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.1 in 9
  have eq54 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq26 eq12 -- superposition 12,26, 26 into 12, unify on (0).2 in 26 and (0).2.2 in 12
  have eq86 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq49 eq49 -- superposition 49,49, 49 into 49, unify on (0).2 in 49 and (0).1.1 in 49
  have eq149 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq86 eq12 -- superposition 12,86, 86 into 12, unify on (0).2 in 86 and (0).1 in 12
  have eq150 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq86 eq9 -- superposition 9,86, 86 into 9, unify on (0).2 in 86 and (0).1.1.1 in 9
  have eq234 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) := superpose eq150 eq19 -- superposition 19,150, 150 into 19, unify on (0).2 in 150 and (0).1.1.1.2 in 19
  have eq235 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq150 eq26 -- superposition 26,150, 150 into 26, unify on (0).2 in 150 and (0).1.1.2 in 26
  have eq309 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq150 eq42 -- superposition 42,150, 150 into 42, unify on (0).2 in 150 and (0).1.1 in 42
  have eq365 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) ◇ X3) ◇ X0) := superpose eq42 eq11 -- superposition 11,42, 42 into 11, unify on (0).2 in 42 and (0).2.1 in 11
  have eq402 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq309 eq235 -- backward demodulation 235,309
  have eq404 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq402 eq234 -- backward demodulation 234,402
  have eq407 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq404 eq15 -- backward demodulation 15,404
  have eq412 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) := superpose eq407 eq54 -- backward demodulation 54,407
  have eq432 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq149 eq412 -- forward demodulation 412,149
  have eq557 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X2) = (((((X0 ◇ X0) ◇ X2) ◇ X3) ◇ X3) ◇ X0) := superpose eq432 eq365 -- forward demodulation 365,432
  have eq558 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X2) ◇ X0) := superpose eq309 eq557 -- forward demodulation 557,309
  have eq559 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq558 eq10 -- backward demodulation 10,558
  subsumption eq559 eq150


@[equational_result]
theorem Equation2860_implies_Equation4282 (G : Type*) [Magma G] (h : Equation2860 G) : Equation4282 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq18 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq19 (X0 X1 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3)) = X0 := superpose eq15 eq18 -- forward demodulation 18,15
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq42 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X3) ◇ X3) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq49 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.1 in 9
  have eq54 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq26 eq12 -- superposition 12,26, 26 into 12, unify on (0).2 in 26 and (0).2.2 in 12
  have eq86 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq49 eq49 -- superposition 49,49, 49 into 49, unify on (0).2 in 49 and (0).1.1 in 49
  have eq143 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq86 eq12 -- superposition 12,86, 86 into 12, unify on (0).2 in 86 and (0).1 in 12
  have eq144 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq86 eq9 -- superposition 9,86, 86 into 9, unify on (0).2 in 86 and (0).1.1.1 in 9
  have eq234 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) := superpose eq144 eq19 -- superposition 19,144, 144 into 19, unify on (0).2 in 144 and (0).1.1.1.2 in 19
  have eq235 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq144 eq26 -- superposition 26,144, 144 into 26, unify on (0).2 in 144 and (0).1.1.2 in 26
  have eq309 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq144 eq42 -- superposition 42,144, 144 into 42, unify on (0).2 in 144 and (0).1.1 in 42
  have eq402 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq309 eq235 -- backward demodulation 235,309
  have eq404 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq402 eq234 -- backward demodulation 234,402
  have eq407 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq404 eq15 -- backward demodulation 15,404
  have eq412 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) := superpose eq407 eq54 -- backward demodulation 54,407
  have eq432 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq143 eq412 -- forward demodulation 412,143
  have eq467 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ sK0) := superpose eq432 eq10 -- backward demodulation 10,432
  subsumption eq467 eq432


@[equational_result]
theorem Equation2860_implies_Equation3457 (G : Type*) [Magma G] (h : Equation2860 G) : Equation3457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq49 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.1 in 9
  have eq86 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq49 eq49 -- superposition 49,49, 49 into 49, unify on (0).2 in 49 and (0).1.1 in 49
  have eq149 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq86 eq12 -- superposition 12,86, 86 into 12, unify on (0).2 in 86 and (0).1 in 12
  have eq1209 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq149 eq10 -- superposition 10,149, 149 into 10, unify on (0).2 in 149 and (0).2 in 10
  subsumption eq1209 rfl


@[equational_result]
theorem Equation2860_implies_Equation2646 (G : Type*) [Magma G] (h : Equation2860 G) : Equation2646 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq17 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq19 (X0 X1 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3)) = X0 := superpose eq15 eq17 -- forward demodulation 17,15
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq42 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X3) ◇ X3) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq49 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.1 in 9
  have eq54 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq26 eq12 -- superposition 12,26, 26 into 12, unify on (0).2 in 26 and (0).2.2 in 12
  have eq86 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq49 eq49 -- superposition 49,49, 49 into 49, unify on (0).2 in 49 and (0).1.1 in 49
  have eq149 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq86 eq12 -- superposition 12,86, 86 into 12, unify on (0).2 in 86 and (0).1 in 12
  have eq150 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq86 eq9 -- superposition 9,86, 86 into 9, unify on (0).2 in 86 and (0).1.1.1 in 9
  have eq234 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) := superpose eq150 eq19 -- superposition 19,150, 150 into 19, unify on (0).2 in 150 and (0).1.1.1.2 in 19
  have eq235 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq150 eq26 -- superposition 26,150, 150 into 26, unify on (0).2 in 150 and (0).1.1.2 in 26
  have eq309 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq150 eq42 -- superposition 42,150, 150 into 42, unify on (0).2 in 150 and (0).1.1 in 42
  have eq402 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq309 eq235 -- backward demodulation 235,309
  have eq404 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq402 eq234 -- backward demodulation 234,402
  have eq407 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq404 eq15 -- backward demodulation 15,404
  have eq412 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) := superpose eq407 eq54 -- backward demodulation 54,407
  have eq432 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq149 eq412 -- forward demodulation 412,149
  have eq465 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose eq432 eq407 -- backward demodulation 407,432
  have eq476 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq465 eq10 -- backward demodulation 10,465
  subsumption eq476 eq49


@[equational_result]
theorem Equation2860_implies_Equation308 (G : Type*) [Magma G] (h : Equation2860 G) : Equation308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq18 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq19 (X0 X1 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3)) = X0 := superpose eq15 eq18 -- forward demodulation 18,15
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq42 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X3) ◇ X3) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq49 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.1 in 9
  have eq54 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq26 eq12 -- superposition 12,26, 26 into 12, unify on (0).2 in 26 and (0).2.2 in 12
  have eq86 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq49 eq49 -- superposition 49,49, 49 into 49, unify on (0).2 in 49 and (0).1.1 in 49
  have eq143 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq86 eq12 -- superposition 12,86, 86 into 12, unify on (0).2 in 86 and (0).1 in 12
  have eq144 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq86 eq9 -- superposition 9,86, 86 into 9, unify on (0).2 in 86 and (0).1.1.1 in 9
  have eq234 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) := superpose eq144 eq19 -- superposition 19,144, 144 into 19, unify on (0).2 in 144 and (0).1.1.1.2 in 19
  have eq235 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq144 eq26 -- superposition 26,144, 144 into 26, unify on (0).2 in 144 and (0).1.1.2 in 26
  have eq309 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq144 eq42 -- superposition 42,144, 144 into 42, unify on (0).2 in 144 and (0).1.1 in 42
  have eq402 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq309 eq235 -- backward demodulation 235,309
  have eq404 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq402 eq234 -- backward demodulation 234,402
  have eq407 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq404 eq15 -- backward demodulation 15,404
  have eq412 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) := superpose eq407 eq54 -- backward demodulation 54,407
  have eq432 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq143 eq412 -- forward demodulation 412,143
  have eq605 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq432 eq10 -- superposition 10,432, 432 into 10, unify on (0).2 in 432 and (0).1 in 10
  subsumption eq605 rfl


@[equational_result]
theorem Equation2860_implies_Equation2663 (G : Type*) [Magma G] (h : Equation2860 G) : Equation2663 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq17 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq19 (X0 X1 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3)) = X0 := superpose eq15 eq17 -- forward demodulation 17,15
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq30 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3)) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.2 in 12
  have eq42 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X3) ◇ X3) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq49 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.1 in 9
  have eq54 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq26 eq12 -- superposition 12,26, 26 into 12, unify on (0).2 in 26 and (0).2.2 in 12
  have eq86 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq49 eq49 -- superposition 49,49, 49 into 49, unify on (0).2 in 49 and (0).1.1 in 49
  have eq144 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0))) := superpose eq86 eq11 -- superposition 11,86, 86 into 11, unify on (0).2 in 86 and (0).2.1 in 11
  have eq149 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq86 eq12 -- superposition 12,86, 86 into 12, unify on (0).2 in 86 and (0).1 in 12
  have eq150 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq86 eq9 -- superposition 9,86, 86 into 9, unify on (0).2 in 86 and (0).1.1.1 in 9
  have eq234 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) := superpose eq150 eq19 -- superposition 19,150, 150 into 19, unify on (0).2 in 150 and (0).1.1.1.2 in 19
  have eq235 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq150 eq26 -- superposition 26,150, 150 into 26, unify on (0).2 in 150 and (0).1.1.2 in 26
  have eq309 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq150 eq42 -- superposition 42,150, 150 into 42, unify on (0).2 in 150 and (0).1.1 in 42
  have eq402 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq309 eq235 -- backward demodulation 235,309
  have eq404 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq402 eq234 -- backward demodulation 234,402
  have eq407 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq404 eq15 -- backward demodulation 15,404
  have eq412 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) := superpose eq407 eq54 -- backward demodulation 54,407
  have eq432 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq149 eq412 -- forward demodulation 412,149
  have eq440 (X0 X2 X3 : G) : ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ X3)) = ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq432 eq30 -- backward demodulation 30,432
  have eq457 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = (((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ (((X0 ◇ X0) ◇ X2) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ (((X0 ◇ X0) ◇ X2) ◇ X0))) := superpose eq432 eq144 -- backward demodulation 144,432
  have eq467 (X0 X2 X3 : G) : (X0 ◇ X2) = ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ X3)) := superpose eq402 eq440 -- forward demodulation 440,402
  have eq631 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) := superpose eq86 eq467 -- superposition 467,86, 86 into 467, unify on (0).2 in 86 and (0).2 in 467
  have eq650 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq631 eq457 -- backward demodulation 457,631
  have eq651 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq650 eq10 -- backward demodulation 10,650
  subsumption eq651 eq150


@[equational_result]
theorem Equation3270_implies_Equation3297 (G : Type*) [Magma G] (h : Equation3270 G) : Equation3297 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq14 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq56 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq13 -- superposition 13,28, 28 into 13, unify on (0).2 in 28 and (0).2 in 13
  subsumption eq56 eq28


@[equational_result]
theorem Equation3270_implies_Equation3281 (G : Type*) [Magma G] (h : Equation3270 G) : Equation3281 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq14 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq56 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq13 -- superposition 13,28, 28 into 13, unify on (0).2 in 28 and (0).2 in 13
  subsumption eq56 eq28


@[equational_result]
theorem Equation3270_implies_Equation3674 (G : Type*) [Magma G] (h : Equation3270 G) : Equation3674 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation3270_implies_Equation3664 (G : Type*) [Magma G] (h : Equation3270 G) : Equation3664 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation3270_implies_Equation3283 (G : Type*) [Magma G] (h : Equation3270 G) : Equation3283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq14 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq56 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq13 -- superposition 13,28, 28 into 13, unify on (0).2 in 28 and (0).2 in 13
  subsumption eq56 eq28


@[equational_result]
theorem Equation3270_implies_Equation3263 (G : Type*) [Magma G] (h : Equation3270 G) : Equation3263 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq14 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq56 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq13 -- superposition 13,28, 28 into 13, unify on (0).2 in 28 and (0).2 in 13
  subsumption eq56 eq28


@[equational_result]
theorem Equation3270_implies_Equation3296 (G : Type*) [Magma G] (h : Equation3270 G) : Equation3296 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq14 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq56 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq13 -- superposition 13,28, 28 into 13, unify on (0).2 in 28 and (0).2 in 13
  subsumption eq56 eq28


@[equational_result]
theorem Equation3270_implies_Equation3299 (G : Type*) [Magma G] (h : Equation3270 G) : Equation3299 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq14 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq56 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq13 -- superposition 13,28, 28 into 13, unify on (0).2 in 28 and (0).2 in 13
  subsumption eq56 eq28


@[equational_result]
theorem Equation1405_implies_Equation4006 (G : Type*) [Magma G] (h : Equation1405 G) : Equation4006 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : (X4 ◇ ((X3 ◇ X4) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X3) = (X1 ◇ X3) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq106 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq106 rfl


@[equational_result]
theorem Equation1405_implies_Equation2161 (G : Type*) [Magma G] (h : Equation1405 G) : Equation2161 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : (X4 ◇ ((X3 ◇ X4) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ X4) ◇ (X4 ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ X4) = (X1 ◇ X4) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X1 X4 X5 : G) : ((X1 ◇ X4) ◇ (X4 ◇ X5)) = X5 := superpose eq16 eq12 -- backward demodulation 12,16
  have eq28 : sK0 ≠ sK0 := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq28 rfl


@[equational_result]
theorem Equation1405_implies_Equation127 (G : Type*) [Magma G] (h : Equation1405 G) : Equation127 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : (X4 ◇ ((X3 ◇ X4) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1405_implies_Equation4040 (G : Type*) [Magma G] (h : Equation1405 G) : Equation4040 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : (X4 ◇ ((X3 ◇ X4) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X3) = (X1 ◇ X3) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq106 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq106 rfl


@[equational_result]
theorem Equation1405_implies_Equation3972 (G : Type*) [Magma G] (h : Equation1405 G) : Equation3972 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : (X4 ◇ ((X3 ◇ X4) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X3) = (X1 ◇ X3) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq106 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq106 rfl


@[equational_result]
theorem Equation1405_implies_Equation138 (G : Type*) [Magma G] (h : Equation1405 G) : Equation138 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : (X4 ◇ ((X3 ◇ X4) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation1405_implies_Equation2063 (G : Type*) [Magma G] (h : Equation1405 G) : Equation2063 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : (X4 ◇ ((X3 ◇ X4) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ X4) ◇ (X4 ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ X4) = (X1 ◇ X4) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X1 X4 X5 : G) : ((X1 ◇ X4) ◇ (X4 ◇ X5)) = X5 := superpose eq16 eq12 -- backward demodulation 12,16
  have eq28 : sK0 ≠ sK0 := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq28 rfl


@[equational_result]
theorem Equation3490_implies_Equation3262 (G : Type*) [Magma G] (h : Equation3490 G) : Equation3262 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X2) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq15 (X0 X4 X5 : G) : (X5 ◇ X5) = (X0 ◇ (X4 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq58 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq58 eq15


@[equational_result]
theorem Equation3490_implies_Equation3473 (G : Type*) [Magma G] (h : Equation3490 G) : Equation3473 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X2) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq13 (X0 X3 X4 X5 : G) : (X4 ◇ X4) = (X0 ◇ ((X3 ◇ X3) ◇ X5)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq26 (X0 : G) : (X0 ◇ X0) ≠ (sK1 ◇ ((X0 ◇ X0) ◇ sK2)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).1 in 10
  subsumption eq26 eq13


@[equational_result]
theorem Equation3490_implies_Equation3256 (G : Type*) [Magma G] (h : Equation3490 G) : Equation3256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X2) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq15 (X0 X4 X5 : G) : (X5 ◇ X5) = (X0 ◇ (X4 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq58 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq58 eq15


@[equational_result]
theorem Equation3740_implies_Equation4131 (G : Type*) [Magma G] (h : Equation3740 G) : Equation4131 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X2) ◇ (X2 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq47 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq12 eq17 -- superposition 17,12, 12 into 17, unify on (0).2 in 12 and (0).1 in 17
  have eq151 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X2))) = ((X3 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq9 eq47 -- superposition 47,9, 9 into 47, unify on (0).2 in 9 and (0).2.2 in 47
  have eq158 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ X2)) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  have eq193 (X1 X2 X3 : G) : (X3 ◇ X2) = (X3 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq151 -- forward demodulation 151,9
  have eq276 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := superpose eq158 eq10 -- backward demodulation 10,158
  have eq603 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := superpose eq158 eq276 -- superposition 276,158, 158 into 276, unify on (0).2 in 158 and (0).2 in 276
  have eq616 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := superpose eq158 eq603 -- forward demodulation 603,158
  subsumption eq616 eq193


@[equational_result]
theorem Equation3740_implies_Equation4073 (G : Type*) [Magma G] (h : Equation3740 G) : Equation4073 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X2) ◇ (X2 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq47 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq12 eq17 -- superposition 17,12, 12 into 17, unify on (0).2 in 12 and (0).1 in 17
  have eq151 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X2))) = ((X3 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq9 eq47 -- superposition 47,9, 9 into 47, unify on (0).2 in 9 and (0).2.2 in 47
  have eq158 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ X2)) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  have eq193 (X1 X2 X3 : G) : (X3 ◇ X2) = (X3 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq151 -- forward demodulation 151,9
  have eq276 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := superpose eq158 eq10 -- backward demodulation 10,158
  have eq603 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := superpose eq158 eq276 -- superposition 276,158, 158 into 276, unify on (0).2 in 158 and (0).2 in 276
  have eq616 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := superpose eq158 eq603 -- forward demodulation 603,158
  subsumption eq616 eq193


@[equational_result]
theorem Equation3740_implies_Equation4146 (G : Type*) [Magma G] (h : Equation3740 G) : Equation4146 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X2) ◇ (X2 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq47 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq12 eq17 -- superposition 17,12, 12 into 17, unify on (0).2 in 12 and (0).1 in 17
  have eq151 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X2))) = ((X3 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq9 eq47 -- superposition 47,9, 9 into 47, unify on (0).2 in 9 and (0).2.2 in 47
  have eq158 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ X2)) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  have eq193 (X1 X2 X3 : G) : (X3 ◇ X2) = (X3 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq151 -- forward demodulation 151,9
  have eq276 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK1) := superpose eq158 eq10 -- backward demodulation 10,158
  have eq603 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK2) ◇ sK1)) := superpose eq158 eq276 -- superposition 276,158, 158 into 276, unify on (0).2 in 158 and (0).2 in 276
  have eq616 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := superpose eq158 eq603 -- forward demodulation 603,158
  subsumption eq616 eq193


@[equational_result]
theorem Equation3740_implies_Equation3261 (G : Type*) [Magma G] (h : Equation3740 G) : Equation3261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X2) ◇ (X2 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq47 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq12 eq17 -- superposition 17,12, 12 into 17, unify on (0).2 in 12 and (0).1 in 17
  have eq151 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X2))) = ((X3 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq9 eq47 -- superposition 47,9, 9 into 47, unify on (0).2 in 9 and (0).2.2 in 47
  have eq193 (X1 X2 X3 : G) : (X3 ◇ X2) = (X3 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq151 -- forward demodulation 151,9
  have eq753 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq193 eq10 -- superposition 10,193, 193 into 10, unify on (0).2 in 193 and (0).2 in 10
  subsumption eq753 rfl


@[equational_result]
theorem Equation3740_implies_Equation4435 (G : Type*) [Magma G] (h : Equation3740 G) : Equation4435 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X2) ◇ (X2 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq47 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq12 eq17 -- superposition 17,12, 12 into 17, unify on (0).2 in 12 and (0).1 in 17
  have eq158 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ X2)) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  have eq638 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq158 eq10 -- superposition 10,158, 158 into 10, unify on (0).2 in 158 and (0).2 in 10
  subsumption eq638 rfl


@[equational_result]
theorem Equation3740_implies_Equation3334 (G : Type*) [Magma G] (h : Equation3740 G) : Equation3334 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X2) ◇ (X2 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq47 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq12 eq17 -- superposition 17,12, 12 into 17, unify on (0).2 in 12 and (0).1 in 17
  have eq151 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X2))) = ((X3 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq9 eq47 -- superposition 47,9, 9 into 47, unify on (0).2 in 9 and (0).2.2 in 47
  have eq193 (X1 X2 X3 : G) : (X3 ◇ X2) = (X3 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq151 -- forward demodulation 151,9
  have eq753 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq193 eq10 -- superposition 10,193, 193 into 10, unify on (0).2 in 193 and (0).2 in 10
  subsumption eq753 rfl


@[equational_result]
theorem Equation3740_implies_Equation3319 (G : Type*) [Magma G] (h : Equation3740 G) : Equation3319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X2) ◇ (X2 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq47 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq12 eq17 -- superposition 17,12, 12 into 17, unify on (0).2 in 12 and (0).1 in 17
  have eq151 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X2))) = ((X3 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq9 eq47 -- superposition 47,9, 9 into 47, unify on (0).2 in 9 and (0).2.2 in 47
  have eq193 (X1 X2 X3 : G) : (X3 ◇ X2) = (X3 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq151 -- forward demodulation 151,9
  have eq753 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq193 eq10 -- superposition 10,193, 193 into 10, unify on (0).2 in 193 and (0).2 in 10
  subsumption eq753 rfl


@[equational_result]
theorem Equation3740_implies_Equation3306 (G : Type*) [Magma G] (h : Equation3740 G) : Equation3306 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X2) ◇ (X2 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq47 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq12 eq17 -- superposition 17,12, 12 into 17, unify on (0).2 in 12 and (0).1 in 17
  have eq151 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X2))) = ((X3 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq9 eq47 -- superposition 47,9, 9 into 47, unify on (0).2 in 9 and (0).2.2 in 47
  have eq193 (X1 X2 X3 : G) : (X3 ◇ X2) = (X3 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq151 -- forward demodulation 151,9
  have eq737 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq193 eq10 -- superposition 10,193, 193 into 10, unify on (0).2 in 193 and (0).2 in 10
  subsumption eq737 rfl


@[equational_result]
theorem Equation3740_implies_Equation4118 (G : Type*) [Magma G] (h : Equation3740 G) : Equation4118 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X2) ◇ (X2 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq47 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq12 eq17 -- superposition 17,12, 12 into 17, unify on (0).2 in 12 and (0).1 in 17
  have eq151 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X2))) = ((X3 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq9 eq47 -- superposition 47,9, 9 into 47, unify on (0).2 in 9 and (0).2.2 in 47
  have eq158 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ X2)) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  have eq193 (X1 X2 X3 : G) : (X3 ◇ X2) = (X3 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq151 -- forward demodulation 151,9
  have eq276 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := superpose eq158 eq10 -- backward demodulation 10,158
  have eq603 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := superpose eq158 eq276 -- superposition 276,158, 158 into 276, unify on (0).2 in 158 and (0).2 in 276
  have eq616 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := superpose eq158 eq603 -- forward demodulation 603,158
  subsumption eq616 eq193


@[equational_result]
theorem Equation3740_implies_Equation4473 (G : Type*) [Magma G] (h : Equation3740 G) : Equation4473 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X2) ◇ (X2 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq47 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq12 eq17 -- superposition 17,12, 12 into 17, unify on (0).2 in 12 and (0).1 in 17
  have eq158 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ X2)) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  have eq646 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq158 eq10 -- superposition 10,158, 158 into 10, unify on (0).2 in 158 and (0).2 in 10
  subsumption eq646 rfl


@[equational_result]
theorem Equation3740_implies_Equation4396 (G : Type*) [Magma G] (h : Equation3740 G) : Equation4396 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X2) ◇ (X2 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq47 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq12 eq17 -- superposition 17,12, 12 into 17, unify on (0).2 in 12 and (0).1 in 17
  have eq158 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ X2)) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  have eq638 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq158 eq10 -- superposition 10,158, 158 into 10, unify on (0).2 in 158 and (0).2 in 10
  subsumption eq638 rfl


@[equational_result]
theorem Equation3740_implies_Equation4512 (G : Type*) [Magma G] (h : Equation3740 G) : Equation4512 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X2) ◇ (X2 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq47 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq12 eq17 -- superposition 17,12, 12 into 17, unify on (0).2 in 12 and (0).1 in 17
  have eq158 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  have eq638 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq158 eq10 -- superposition 10,158, 158 into 10, unify on (0).2 in 158 and (0).2 in 10
  subsumption eq638 rfl


@[equational_result]
theorem Equation1871_implies_Equation1657 (G : Type*) [Magma G] (h : Equation1871 G) : Equation1657 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ ((X4 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1.2 in 11
  have eq50 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1871_implies_Equation1654 (G : Type*) [Magma G] (h : Equation1871 G) : Equation1654 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ ((X4 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1.2 in 11
  have eq50 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1871_implies_Equation1631 (G : Type*) [Magma G] (h : Equation1871 G) : Equation1631 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ ((X4 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1.2 in 11
  have eq50 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1871_implies_Equation1660 (G : Type*) [Magma G] (h : Equation1871 G) : Equation1660 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ ((X4 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1.2 in 11
  have eq50 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation3493_implies_Equation3477 (G : Type*) [Magma G] (h : Equation3493 G) : Equation3477 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK0 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq54 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq17 -- superposition 17,27, 27 into 17, unify on (0).2 in 27 and (0).2 in 17
  subsumption eq54 eq27


@[equational_result]
theorem Equation3493_implies_Equation3256 (G : Type*) [Magma G] (h : Equation3493 G) : Equation3256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq35 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq35 eq15


@[equational_result]
theorem Equation3493_implies_Equation3488 (G : Type*) [Magma G] (h : Equation3493 G) : Equation3488 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq54 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq17 -- superposition 17,27, 27 into 17, unify on (0).2 in 27 and (0).2 in 17
  subsumption eq54 eq27


@[equational_result]
theorem Equation3493_implies_Equation3500 (G : Type*) [Magma G] (h : Equation3493 G) : Equation3500 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = (X3 ◇ ((X2 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ ((X2 ◇ X2) ◇ X0)) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq26 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq54 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq54 eq26


@[equational_result]
theorem Equation3493_implies_Equation3678 (G : Type*) [Magma G] (h : Equation3493 G) : Equation3678 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq26 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq32 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq32 eq26


@[equational_result]
theorem Equation3493_implies_Equation3497 (G : Type*) [Magma G] (h : Equation3493 G) : Equation3497 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq54 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq17 -- superposition 17,27, 27 into 17, unify on (0).2 in 27 and (0).2 in 17
  subsumption eq54 eq27


@[equational_result]
theorem Equation3493_implies_Equation3472 (G : Type*) [Magma G] (h : Equation3493 G) : Equation3472 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = (X3 ◇ ((X2 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq17 (X0 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ ((X2 ◇ X2) ◇ X0)) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq54 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq54 rfl


@[equational_result]
theorem Equation3493_implies_Equation3662 (G : Type*) [Magma G] (h : Equation3493 G) : Equation3662 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq26 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq34 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq34 eq26


@[equational_result]
theorem Equation3493_implies_Equation3262 (G : Type*) [Magma G] (h : Equation3493 G) : Equation3262 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq35 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq35 eq15


@[equational_result]
theorem Equation3493_implies_Equation3468 (G : Type*) [Magma G] (h : Equation3493 G) : Equation3468 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq54 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq17 -- superposition 17,27, 27 into 17, unify on (0).2 in 27 and (0).2 in 17
  subsumption eq54 eq27


@[equational_result]
theorem Equation3493_implies_Equation3505 (G : Type*) [Magma G] (h : Equation3493 G) : Equation3505 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ sK2)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq54 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq17 -- superposition 17,27, 27 into 17, unify on (0).2 in 27 and (0).2 in 17
  subsumption eq54 eq27


@[equational_result]
theorem Equation4545_implies_Equation4499 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4499 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq35 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq47 (X1 : G) : ((sK2 ◇ sK2) ◇ sK2) ≠ (X1 ◇ (sK1 ◇ sK1)) := superpose eq9 eq35 -- superposition 35,9, 9 into 35, unify on (0).2 in 9 and (0).1 in 35
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq217 (X0 X1 X2 : G) : ((sK2 ◇ sK2) ◇ sK2) ≠ (X2 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  subsumption eq217 eq75


@[equational_result]
theorem Equation4545_implies_Equation4658 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4658 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X0 X1 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ (X1 ◇ ((sK0 ◇ sK1) ◇ X0)) := superpose eq9 eq18 -- superposition 18,9, 9 into 18, unify on (0).2 in 9 and (0).2 in 18
  have eq72 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ X0) = (X5 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).2.2 in 13
  have eq144 (X0 X1 X2 X3 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq16 eq21 -- superposition 21,16, 16 into 21, unify on (0).2 in 16 and (0).2.2 in 21
  subsumption eq144 eq72


@[equational_result]
theorem Equation4545_implies_Equation4479 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4479 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq35 (X0 X1 : G) : (X1 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq51 (X1 : G) : ((sK1 ◇ sK1) ◇ sK1) ≠ (X1 ◇ (sK0 ◇ sK1)) := superpose eq9 eq35 -- superposition 35,9, 9 into 35, unify on (0).2 in 9 and (0).2 in 35
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq217 (X0 X1 X2 : G) : ((sK1 ◇ sK1) ◇ sK1) ≠ (X2 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq51 -- superposition 51,11, 11 into 51, unify on (0).2 in 11 and (0).2 in 51
  subsumption eq217 eq75


@[equational_result]
theorem Equation4545_implies_Equation4504 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4504 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK3 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq35 (X0 X1 : G) : (X1 ◇ (sK3 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq47 (X1 : G) : ((sK2 ◇ sK3) ◇ sK3) ≠ (X1 ◇ (sK1 ◇ sK1)) := superpose eq9 eq35 -- superposition 35,9, 9 into 35, unify on (0).2 in 9 and (0).1 in 35
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq217 (X0 X1 X2 : G) : ((sK2 ◇ sK3) ◇ sK3) ≠ (X2 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  subsumption eq217 eq75


@[equational_result]
theorem Equation4545_implies_Equation4432 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4432 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK0 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq35 (X0 X1 : G) : (X1 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK0)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq51 (X1 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ (X1 ◇ (sK0 ◇ sK0)) := superpose eq9 eq35 -- superposition 35,9, 9 into 35, unify on (0).2 in 9 and (0).2 in 35
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq217 (X0 X1 X2 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ (X2 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq51 -- superposition 51,11, 11 into 51, unify on (0).2 in 11 and (0).2 in 51
  subsumption eq217 eq75


@[equational_result]
theorem Equation4545_implies_Equation4670 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4670 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK2 ◇ sK3) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ (X0 ◇ (sK3 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X0 X1 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ (X1 ◇ ((sK3 ◇ sK2) ◇ X0)) := superpose eq9 eq18 -- superposition 18,9, 9 into 18, unify on (0).2 in 9 and (0).2 in 18
  have eq72 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ X0) = (X5 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).2.2 in 13
  have eq143 (X0 X1 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ (X1 ◇ (X0 ◇ (sK2 ◇ sK3))) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2.2 in 21
  subsumption eq143 eq72


@[equational_result]
theorem Equation4545_implies_Equation4440 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4440 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq35 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK0)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq47 (X1 : G) : ((sK0 ◇ sK2) ◇ sK2) ≠ (X1 ◇ (sK1 ◇ sK0)) := superpose eq9 eq35 -- superposition 35,9, 9 into 35, unify on (0).2 in 9 and (0).1 in 35
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq217 (X0 X1 X2 : G) : ((sK0 ◇ sK2) ◇ sK2) ≠ (X2 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  subsumption eq217 eq75


@[equational_result]
theorem Equation4545_implies_Equation4409 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4409 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq35 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq47 (X1 : G) : ((sK1 ◇ sK1) ◇ sK1) ≠ (X1 ◇ (sK0 ◇ sK1)) := superpose eq9 eq35 -- superposition 35,9, 9 into 35, unify on (0).2 in 9 and (0).1 in 35
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq217 (X0 X1 X2 : G) : ((sK1 ◇ sK1) ◇ sK1) ≠ (X2 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  subsumption eq217 eq75


@[equational_result]
theorem Equation4545_implies_Equation4550 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4550 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK2 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq35 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq47 (X1 : G) : ((sK2 ◇ sK2) ◇ sK2) ≠ (X1 ◇ (sK1 ◇ sK2)) := superpose eq9 eq35 -- superposition 35,9, 9 into 35, unify on (0).2 in 9 and (0).1 in 35
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq217 (X0 X1 X2 : G) : ((sK2 ◇ sK2) ◇ sK2) ≠ (X2 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  subsumption eq217 eq75


@[equational_result]
theorem Equation4545_implies_Equation4511 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4511 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq35 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq51 (X1 : G) : ((sK2 ◇ sK1) ◇ sK1) ≠ (X1 ◇ (sK1 ◇ sK0)) := superpose eq9 eq35 -- superposition 35,9, 9 into 35, unify on (0).2 in 9 and (0).2 in 35
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq216 (X0 X1 X2 : G) : ((sK2 ◇ sK1) ◇ sK1) ≠ (X2 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq51 -- superposition 51,11, 11 into 51, unify on (0).2 in 11 and (0).2 in 51
  subsumption eq216 eq75


@[equational_result]
theorem Equation4545_implies_Equation4523 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4523 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq35 (X0 X1 : G) : (X1 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq51 (X1 : G) : ((sK2 ◇ sK1) ◇ sK1) ≠ (X1 ◇ (sK0 ◇ sK1)) := superpose eq9 eq35 -- superposition 35,9, 9 into 35, unify on (0).2 in 9 and (0).2 in 35
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq217 (X0 X1 X2 : G) : ((sK2 ◇ sK1) ◇ sK1) ≠ (X2 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq51 -- superposition 51,11, 11 into 51, unify on (0).2 in 11 and (0).2 in 51
  subsumption eq217 eq75


@[equational_result]
theorem Equation4545_implies_Equation4462 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4462 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq35 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK0)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq47 (X1 : G) : ((sK2 ◇ sK2) ◇ sK2) ≠ (X1 ◇ (sK1 ◇ sK0)) := superpose eq9 eq35 -- superposition 35,9, 9 into 35, unify on (0).2 in 9 and (0).1 in 35
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq217 (X0 X1 X2 : G) : ((sK2 ◇ sK2) ◇ sK2) ≠ (X2 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  subsumption eq217 eq75


@[equational_result]
theorem Equation4545_implies_Equation4538 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4538 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK3) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK3 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq35 (X0 X1 : G) : (X1 ◇ (sK3 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq47 (X1 : G) : ((sK1 ◇ sK3) ◇ sK3) ≠ (X1 ◇ (sK1 ◇ sK2)) := superpose eq9 eq35 -- superposition 35,9, 9 into 35, unify on (0).2 in 9 and (0).1 in 35
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq217 (X0 X1 X2 : G) : ((sK1 ◇ sK3) ◇ sK3) ≠ (X2 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  subsumption eq217 eq75


@[equational_result]
theorem Equation4545_implies_Equation4430 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4430 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK3 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq35 (X0 X1 : G) : (X1 ◇ (sK3 ◇ sK2)) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq47 (X1 : G) : ((sK2 ◇ sK3) ◇ sK3) ≠ (X1 ◇ (sK0 ◇ sK1)) := superpose eq9 eq35 -- superposition 35,9, 9 into 35, unify on (0).2 in 9 and (0).1 in 35
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq217 (X0 X1 X2 : G) : ((sK2 ◇ sK3) ◇ sK3) ≠ (X2 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  subsumption eq217 eq75


@[equational_result]
theorem Equation4545_implies_Equation4399 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4399 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq35 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq47 (X1 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ (X1 ◇ (sK0 ◇ sK1)) := superpose eq9 eq35 -- superposition 35,9, 9 into 35, unify on (0).2 in 9 and (0).1 in 35
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq217 (X0 X1 X2 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ (X2 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  subsumption eq217 eq75


@[equational_result]
theorem Equation4545_implies_Equation4446 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4446 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq35 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK0)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq51 (X1 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ (X1 ◇ (sK1 ◇ sK1)) := superpose eq9 eq35 -- superposition 35,9, 9 into 35, unify on (0).2 in 9 and (0).2 in 35
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq216 (X0 X1 X2 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ (X2 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq51 -- superposition 51,11, 11 into 51, unify on (0).2 in 11 and (0).2 in 51
  subsumption eq216 eq75


@[equational_result]
theorem Equation4545_implies_Equation4494 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4494 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK2 ◇ sK1) ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).1 in 10
  have eq35 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq51 (X1 : G) : ((sK1 ◇ sK1) ◇ sK1) ≠ (X1 ◇ (sK1 ◇ sK2)) := superpose eq9 eq35 -- superposition 35,9, 9 into 35, unify on (0).2 in 9 and (0).2 in 35
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq216 (X0 X1 X2 : G) : ((sK1 ◇ sK1) ◇ sK1) ≠ (X2 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq51 -- superposition 51,11, 11 into 51, unify on (0).2 in 11 and (0).2 in 51
  subsumption eq216 eq75


@[equational_result]
theorem Equation4545_implies_Equation4533 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4533 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK2 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq35 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq47 (X1 : G) : ((sK1 ◇ sK2) ◇ sK2) ≠ (X1 ◇ (sK1 ◇ sK2)) := superpose eq9 eq35 -- superposition 35,9, 9 into 35, unify on (0).2 in 9 and (0).1 in 35
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq217 (X0 X1 X2 : G) : ((sK1 ◇ sK2) ◇ sK2) ≠ (X2 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  subsumption eq217 eq75


@[equational_result]
theorem Equation4545_implies_Equation4420 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4420 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK2 ◇ sK1) ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).1 in 10
  have eq35 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq47 (X1 : G) : ((sK2 ◇ sK1) ◇ sK1) ≠ (X1 ◇ (sK0 ◇ sK1)) := superpose eq9 eq35 -- superposition 35,9, 9 into 35, unify on (0).2 in 9 and (0).1 in 35
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq217 (X0 X1 X2 : G) : ((sK2 ◇ sK1) ◇ sK1) ≠ (X2 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  subsumption eq217 eq75


@[equational_result]
theorem Equation4545_implies_Equation4521 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4521 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK3) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK3 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq35 (X0 X1 : G) : (X1 ◇ (sK3 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq47 (X1 : G) : ((sK0 ◇ sK3) ◇ sK3) ≠ (X1 ◇ (sK1 ◇ sK2)) := superpose eq9 eq35 -- superposition 35,9, 9 into 35, unify on (0).2 in 9 and (0).1 in 35
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq217 (X0 X1 X2 : G) : ((sK0 ◇ sK3) ◇ sK3) ≠ (X2 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  subsumption eq217 eq75


@[equational_result]
theorem Equation3067_implies_Equation3076 (G : Type*) [Magma G] (h : Equation3067 G) : Equation3076 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq21 (X0 X1 X3 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = (X0 ◇ X3) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq69 (X0 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ X2) := superpose eq21 eq21 -- superposition 21,21, 21 into 21, unify on (0).2 in 21 and (0).1 in 21
  have eq160 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X3) = X0 := superpose eq69 eq9 -- superposition 9,69, 69 into 9, unify on (0).2 in 69 and (0).1.1.1 in 9
  have eq177 (X0 : G) : sK0 ≠ ((((sK0 ◇ X0) ◇ sK1) ◇ sK0) ◇ sK1) := superpose eq69 eq10 -- superposition 10,69, 69 into 10, unify on (0).2 in 69 and (0).2.1.1.1 in 10
  subsumption eq177 eq160


@[equational_result]
theorem Equation3875_implies_Equation4068 (G : Type*) [Magma G] (h : Equation3875 G) : Equation4068 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X3 ◇ X3) = ((X3 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq25 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.1 in 13
  have eq34 (X0 X3 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X3) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq39 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq34 eq10 -- backward demodulation 10,34
  subsumption eq39 eq34


@[equational_result]
theorem Equation3875_implies_Equation4069 (G : Type*) [Magma G] (h : Equation3875 G) : Equation4069 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X3 ◇ X3) = ((X3 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq25 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.1 in 13
  have eq34 (X0 X3 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X3) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq39 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq34 eq10 -- backward demodulation 10,34
  subsumption eq39 eq34


@[equational_result]
theorem Equation3875_implies_Equation3661 (G : Type*) [Magma G] (h : Equation3875 G) : Equation3661 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X3 ◇ X3) = ((X3 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq25 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.1 in 13
  have eq34 (X0 X3 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X3) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq100 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq34 eq10 -- superposition 10,34, 34 into 10, unify on (0).2 in 34 and (0).2 in 10
  subsumption eq100 rfl


@[equational_result]
theorem Equation3875_implies_Equation3870 (G : Type*) [Magma G] (h : Equation3875 G) : Equation3870 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X3 ◇ X3) = ((X3 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq31 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq31 rfl


@[equational_result]
theorem Equation3875_implies_Equation360 (G : Type*) [Magma G] (h : Equation3875 G) : Equation360 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X3 ◇ X3) = ((X3 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq25 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.1 in 13
  have eq34 (X0 X3 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X3) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq92 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq34 eq10 -- superposition 10,34, 34 into 10, unify on (0).2 in 34 and (0).2 in 10
  subsumption eq92 rfl


@[equational_result]
theorem Equation3875_implies_Equation3863 (G : Type*) [Magma G] (h : Equation3875 G) : Equation3863 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X3 ◇ X3) = ((X3 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq31 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq31 rfl


@[equational_result]
theorem Equation3875_implies_Equation3872 (G : Type*) [Magma G] (h : Equation3875 G) : Equation3872 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X3 ◇ X3) = ((X3 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq31 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq31 rfl


@[equational_result]
theorem Equation4078_implies_Equation4069 (G : Type*) [Magma G] (h : Equation4078 G) : Equation4069 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X3) ◇ X3) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq19 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) = (((X0 ◇ X0) ◇ X2) ◇ X3) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1 in 14
  have eq21 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X3) = ((X0 ◇ X0) ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq39 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X2) ◇ X3) := superpose eq16 eq19 -- forward demodulation 19,16
  have eq122 (X0 : G) : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ X0) ◇ sK2) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2.1 in 10
  subsumption eq122 eq39


@[equational_result]
theorem Equation1506_implies_Equation4070 (G : Type*) [Magma G] (h : Equation1506 G) : Equation4070 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X1)) = (X1 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X1)) = ((X3 ◇ (X2 ◇ (X2 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq27 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq32 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq27 -- forward demodulation 27,9
  have eq34 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq32 eq9 -- superposition 9,32, 32 into 9, unify on (0).2 in 32 and (0).1.2 in 9
  have eq56 (X1 X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = ((X1 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.1 in 13
  have eq85 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ X0)) := superpose eq24 eq24 -- superposition 24,24, 24 into 24, unify on (0).2 in 24 and (0).2 in 24
  have eq157 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq85 eq34 -- superposition 34,85, 85 into 34, unify on (0).2 in 85 and (0).2.1 in 34
  have eq212 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = (X2 ◇ X2) := superpose eq157 eq56 -- backward demodulation 56,157
  have eq299 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq212 eq10 -- superposition 10,212, 212 into 10, unify on (0).2 in 212 and (0).2 in 10
  subsumption eq299 rfl


@[equational_result]
theorem Equation1506_implies_Equation3867 (G : Type*) [Magma G] (h : Equation1506 G) : Equation3867 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X1)) = (X1 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq27 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq32 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq27 -- forward demodulation 27,9
  have eq34 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq32 eq9 -- superposition 9,32, 32 into 9, unify on (0).2 in 32 and (0).1.2 in 9
  have eq85 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ X0)) := superpose eq24 eq24 -- superposition 24,24, 24 into 24, unify on (0).2 in 24 and (0).2 in 24
  have eq125 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq32 eq85 -- superposition 85,32, 32 into 85, unify on (0).2 in 32 and (0).1 in 85
  have eq365 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq125 eq9 -- superposition 9,125, 125 into 9, unify on (0).2 in 125 and (0).1.1 in 9
  have eq368 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq125 eq85 -- superposition 85,125, 125 into 85, unify on (0).2 in 125 and (0).1.2 in 85
  have eq378 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq368 eq365 -- backward demodulation 365,368
  have eq918 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq378 eq34 -- superposition 34,378, 378 into 34, unify on (0).2 in 378 and (0).2.1 in 34
  have eq1548 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq918 eq10 -- superposition 10,918, 918 into 10, unify on (0).2 in 918 and (0).2 in 10
  subsumption eq1548 rfl


@[equational_result]
theorem Equation1506_implies_Equation4090 (G : Type*) [Magma G] (h : Equation1506 G) : Equation4090 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X1)) = (X1 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X1)) = ((X3 ◇ (X2 ◇ (X2 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq27 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq32 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq27 -- forward demodulation 27,9
  have eq34 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq32 eq9 -- superposition 9,32, 32 into 9, unify on (0).2 in 32 and (0).1.2 in 9
  have eq56 (X1 X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = ((X1 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.1 in 13
  have eq85 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ X0)) := superpose eq24 eq24 -- superposition 24,24, 24 into 24, unify on (0).2 in 24 and (0).2 in 24
  have eq157 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq85 eq34 -- superposition 34,85, 85 into 34, unify on (0).2 in 85 and (0).2.1 in 34
  have eq212 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = (X2 ◇ X2) := superpose eq157 eq56 -- backward demodulation 56,157
  have eq299 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq212 eq10 -- superposition 10,212, 212 into 10, unify on (0).2 in 212 and (0).2 in 10
  subsumption eq299 rfl


@[equational_result]
theorem Equation2998_implies_Equation3456 (G : Type*) [Magma G] (h : Equation2998 G) : Equation3456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) ◇ X3) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq34 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0)) ◇ X3) = X3 := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1.1 in 11
  have eq45 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq8 eq34 -- forward demodulation 34,8
  have eq58 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq45 eq9 -- backward demodulation 9,45
  subsumption eq58 rfl


@[equational_result]
theorem Equation2998_implies_Equation3759 (G : Type*) [Magma G] (h : Equation2998 G) : Equation3759 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq35 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq46 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq9 eq35 -- forward demodulation 35,9
  have eq77 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq46 eq10 -- superposition 10,46, 46 into 10, unify on (0).2 in 46 and (0).2 in 10
  subsumption eq77 rfl


@[equational_result]
theorem Equation2998_implies_Equation2733 (G : Type*) [Magma G] (h : Equation2998 G) : Equation2733 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq35 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq46 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq9 eq35 -- forward demodulation 35,9
  have eq59 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq46 eq10 -- backward demodulation 10,46
  subsumption eq59 eq46


@[equational_result]
theorem Equation2998_implies_Equation2746 (G : Type*) [Magma G] (h : Equation2998 G) : Equation2746 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq35 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq46 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq9 eq35 -- forward demodulation 35,9
  have eq59 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq46 eq10 -- backward demodulation 10,46
  subsumption eq59 eq46


@[equational_result]
theorem Equation2998_implies_Equation4226 (G : Type*) [Magma G] (h : Equation2998 G) : Equation4226 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK2) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq35 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq46 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq9 eq35 -- forward demodulation 35,9
  have eq59 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq46 eq10 -- backward demodulation 10,46
  subsumption eq59 rfl


@[equational_result]
theorem Equation2998_implies_Equation4090 (G : Type*) [Magma G] (h : Equation2998 G) : Equation4090 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq35 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq46 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq9 eq35 -- forward demodulation 35,9
  have eq59 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq46 eq10 -- backward demodulation 10,46
  subsumption eq59 rfl


@[equational_result]
theorem Equation2998_implies_Equation2605 (G : Type*) [Magma G] (h : Equation2998 G) : Equation2605 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK2) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq35 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq46 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq9 eq35 -- forward demodulation 35,9
  have eq59 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq46 eq10 -- backward demodulation 10,46
  subsumption eq59 eq46


@[equational_result]
theorem Equation2998_implies_Equation3659 (G : Type*) [Magma G] (h : Equation2998 G) : Equation3659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) ◇ X3) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq34 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0)) ◇ X3) = X3 := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1.1 in 11
  have eq45 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq8 eq34 -- forward demodulation 34,8
  have eq74 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq45 eq9 -- superposition 9,45, 45 into 9, unify on (0).2 in 45 and (0).2 in 9
  subsumption eq74 rfl


@[equational_result]
theorem Equation2998_implies_Equation4165 (G : Type*) [Magma G] (h : Equation2998 G) : Equation4165 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq35 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq46 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq9 eq35 -- forward demodulation 35,9
  have eq59 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq46 eq10 -- backward demodulation 10,46
  subsumption eq59 rfl


