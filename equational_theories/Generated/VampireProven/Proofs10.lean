import equational_theories.Superposition
import equational_theories.Equations.All
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

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
theorem Equation423_implies_Equation1022 (G : Type*) [Magma G] (h : Equation423 G) : Equation1022 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq17 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2.2 in 9
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq14 eq17 -- forward demodulation 17,14
  have eq40 (X0 X3 : G) : (X3 ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq18 -- superposition 18,9, 9 into 18, unify on (0).2 in 9 and (0).1.2.2 in 18
  have eq58 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq40 eq10 -- backward demodulation 10,40
  subsumption eq58 eq40


@[equational_result]
theorem Equation423_implies_Equation3320 (G : Type*) [Magma G] (h : Equation423 G) : Equation3320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq17 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2.2 in 9
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq14 eq17 -- forward demodulation 17,14
  have eq40 (X0 X3 : G) : (X3 ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq18 -- superposition 18,9, 9 into 18, unify on (0).2 in 9 and (0).1.2.2 in 18
  have eq58 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq40 eq10 -- backward demodulation 10,40
  subsumption eq58 rfl


@[equational_result]
theorem Equation423_implies_Equation421 (G : Type*) [Magma G] (h : Equation423 G) : Equation421 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq17 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2.2 in 9
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq14 eq17 -- forward demodulation 17,14
  have eq58 : sK0 ≠ sK0 := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq58 rfl


@[equational_result]
theorem Equation4243_implies_Equation364 (G : Type*) [Magma G] (h : Equation4243 G) : Equation364 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (X3 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation4243_implies_Equation395 (G : Type*) [Magma G] (h : Equation4243 G) : Equation395 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (X3 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation4243_implies_Equation4040 (G : Type*) [Magma G] (h : Equation4243 G) : Equation4040 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (X3 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK3 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation4243_implies_Equation4689 (G : Type*) [Magma G] (h : Equation4243 G) : Equation4689 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK3 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (X3 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 : ((sK3 ◇ sK1) ◇ sK2) ≠ (sK1 ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation424_implies_Equation423 (G : Type*) [Magma G] (h : Equation424 G) : Equation423 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation425_implies_Equation1021 (G : Type*) [Magma G] (h : Equation425 G) : Equation1021 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X4 : G) : (X4 ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation425_implies_Equation1023 (G : Type*) [Magma G] (h : Equation425 G) : Equation1023 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X4 : G) : (X4 ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation425_implies_Equation1630 (G : Type*) [Magma G] (h : Equation425 G) : Equation1630 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X4 : G) : (X4 ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq12


@[equational_result]
theorem Equation427_implies_Equation1020 (G : Type*) [Magma G] (h : Equation427 G) : Equation1020 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation428_implies_Equation102 (G : Type*) [Magma G] (h : Equation428 G) : Equation102 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq24 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq32 : sK0 ≠ sK0 := superpose eq22 eq24 -- superposition 24,22, 22 into 24, unify on (0).2 in 22 and (0).2 in 24
  subsumption eq32 rfl


@[equational_result]
theorem Equation428_implies_Equation1027 (G : Type*) [Magma G] (h : Equation428 G) : Equation1027 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq33 : sK0 ≠ sK0 := superpose eq23 eq14 -- superposition 14,23, 23 into 14, unify on (0).2 in 23 and (0).2 in 14
  subsumption eq33 rfl


@[equational_result]
theorem Equation428_implies_Equation1036 (G : Type*) [Magma G] (h : Equation428 G) : Equation1036 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.2 in 12
  have eq33 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq32 eq15 -- backward demodulation 15,32
  subsumption eq33 eq12


@[equational_result]
theorem Equation428_implies_Equation105 (G : Type*) [Magma G] (h : Equation428 G) : Equation105 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.2 in 12
  have eq32 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq31 eq10 -- backward demodulation 10,31
  subsumption eq32 eq12


@[equational_result]
theorem Equation428_implies_Equation1067 (G : Type*) [Magma G] (h : Equation428 G) : Equation1067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq24 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq24 rfl


@[equational_result]
theorem Equation428_implies_Equation1229 (G : Type*) [Magma G] (h : Equation428 G) : Equation1229 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.2 in 12
  have eq32 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := superpose eq31 eq10 -- backward demodulation 10,31
  have eq33 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq19 eq32 -- forward demodulation 32,19
  subsumption eq33 eq22


@[equational_result]
theorem Equation428_implies_Equation1232 (G : Type*) [Magma G] (h : Equation428 G) : Equation1232 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq24 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq25 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq19 eq24 -- forward demodulation 24,19
  have eq33 : sK0 ≠ sK0 := superpose eq22 eq25 -- superposition 25,22, 22 into 25, unify on (0).2 in 22 and (0).2 in 25
  subsumption eq33 rfl


@[equational_result]
theorem Equation428_implies_Equation1239 (G : Type*) [Magma G] (h : Equation428 G) : Equation1239 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq24 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.2 in 12
  have eq33 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq32 eq24 -- backward demodulation 24,32
  subsumption eq33 eq12


@[equational_result]
theorem Equation428_implies_Equation1242 (G : Type*) [Magma G] (h : Equation428 G) : Equation1242 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq24 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.2 in 12
  have eq33 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq32 eq24 -- backward demodulation 24,32
  subsumption eq33 eq12


@[equational_result]
theorem Equation428_implies_Equation1249 (G : Type*) [Magma G] (h : Equation428 G) : Equation1249 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.2 in 12
  have eq33 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq32 eq15 -- backward demodulation 15,32
  subsumption eq33 eq12


@[equational_result]
theorem Equation428_implies_Equation1640 (G : Type*) [Magma G] (h : Equation428 G) : Equation1640 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq12


@[equational_result]
theorem Equation428_implies_Equation1843 (G : Type*) [Magma G] (h : Equation428 G) : Equation1843 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq27 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK0)) := superpose eq22 eq10 -- backward demodulation 10,22
  subsumption eq27 eq12


@[equational_result]
theorem Equation428_implies_Equation1849 (G : Type*) [Magma G] (h : Equation428 G) : Equation1849 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq33 : sK0 ≠ sK0 := superpose eq23 eq14 -- superposition 14,23, 23 into 14, unify on (0).2 in 23 and (0).2 in 14
  subsumption eq33 rfl


@[equational_result]
theorem Equation428_implies_Equation2037 (G : Type*) [Magma G] (h : Equation428 G) : Equation2037 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq15 -- forward demodulation 15,13
  subsumption eq16 eq12


@[equational_result]
theorem Equation428_implies_Equation2253 (G : Type*) [Magma G] (h : Equation428 G) : Equation2253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation428_implies_Equation2459 (G : Type*) [Magma G] (h : Equation428 G) : Equation2459 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.2 in 12
  have eq32 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq31 eq10 -- backward demodulation 10,31
  have eq33 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq32 -- forward demodulation 32,12
  subsumption eq33 eq13


@[equational_result]
theorem Equation428_implies_Equation2649 (G : Type*) [Magma G] (h : Equation428 G) : Equation2649 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq13


@[equational_result]
theorem Equation428_implies_Equation2862 (G : Type*) [Magma G] (h : Equation428 G) : Equation2862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq14 -- backward demodulation 14,13
  subsumption eq16 eq13


@[equational_result]
theorem Equation428_implies_Equation3462 (G : Type*) [Magma G] (h : Equation428 G) : Equation3462 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.2 in 12
  have eq33 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq32 eq15 -- backward demodulation 15,32
  subsumption eq33 eq12


@[equational_result]
theorem Equation428_implies_Equation3661 (G : Type*) [Magma G] (h : Equation428 G) : Equation3661 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq12


@[equational_result]
theorem Equation428_implies_Equation3721 (G : Type*) [Magma G] (h : Equation428 G) : Equation3721 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.2 in 12
  have eq44 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq15 -- superposition 15,32, 32 into 15, unify on (0).2 in 32 and (0).2 in 15
  subsumption eq44 rfl


@[equational_result]
theorem Equation428_implies_Equation3725 (G : Type*) [Magma G] (h : Equation428 G) : Equation3725 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq39 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq39 rfl


@[equational_result]
theorem Equation428_implies_Equation377 (G : Type*) [Magma G] (h : Equation428 G) : Equation377 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.2 in 12
  have eq43 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq31 eq10 -- superposition 10,31, 31 into 10, unify on (0).2 in 31 and (0).2 in 10
  subsumption eq43 rfl


@[equational_result]
theorem Equation428_implies_Equation3927 (G : Type*) [Magma G] (h : Equation428 G) : Equation3927 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.2 in 12
  have eq44 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq15 -- superposition 15,32, 32 into 15, unify on (0).2 in 32 and (0).2 in 15
  subsumption eq44 rfl


@[equational_result]
theorem Equation428_implies_Equation3928 (G : Type*) [Magma G] (h : Equation428 G) : Equation3928 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq37 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq37 rfl


@[equational_result]
theorem Equation428_implies_Equation4120 (G : Type*) [Magma G] (h : Equation428 G) : Equation4120 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.2 in 12
  have eq44 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq15 -- superposition 15,32, 32 into 15, unify on (0).2 in 32 and (0).2 in 15
  subsumption eq44 rfl


@[equational_result]
theorem Equation428_implies_Equation4121 (G : Type*) [Magma G] (h : Equation428 G) : Equation4121 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq37 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq37 rfl


@[equational_result]
theorem Equation428_implies_Equation4130 (G : Type*) [Magma G] (h : Equation428 G) : Equation4130 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq24 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.2 in 12
  have eq47 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq24 -- superposition 24,32, 32 into 24, unify on (0).2 in 32 and (0).2 in 24
  subsumption eq47 rfl


@[equational_result]
theorem Equation428_implies_Equation4286 (G : Type*) [Magma G] (h : Equation428 G) : Equation4286 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq33 : sK0 ≠ sK0 := superpose eq23 eq14 -- superposition 14,23, 23 into 14, unify on (0).2 in 23 and (0).2 in 14
  subsumption eq33 rfl


@[equational_result]
theorem Equation428_implies_Equation4432 (G : Type*) [Magma G] (h : Equation428 G) : Equation4432 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq14 -- backward demodulation 14,13
  subsumption eq16 eq13


@[equational_result]
theorem Equation428_implies_Equation4472 (G : Type*) [Magma G] (h : Equation428 G) : Equation4472 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.2 in 12
  have eq44 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq15 -- superposition 15,32, 32 into 15, unify on (0).2 in 32 and (0).2 in 15
  subsumption eq44 rfl


@[equational_result]
theorem Equation428_implies_Equation4473 (G : Type*) [Magma G] (h : Equation428 G) : Equation4473 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq39 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq39 rfl


@[equational_result]
theorem Equation428_implies_Equation4598 (G : Type*) [Magma G] (h : Equation428 G) : Equation4598 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.2 in 12
  have eq44 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq15 -- superposition 15,32, 32 into 15, unify on (0).2 in 32 and (0).2 in 15
  subsumption eq44 rfl


@[equational_result]
theorem Equation428_implies_Equation4599 (G : Type*) [Magma G] (h : Equation428 G) : Equation4599 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq39 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq39 rfl


@[equational_result]
theorem Equation428_implies_Equation4629 (G : Type*) [Magma G] (h : Equation428 G) : Equation4629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq24 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.2 in 12
  have eq47 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq24 -- superposition 24,32, 32 into 24, unify on (0).2 in 32 and (0).2 in 24
  subsumption eq47 rfl


@[equational_result]
theorem Equation428_implies_Equation52 (G : Type*) [Magma G] (h : Equation428 G) : Equation52 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq12


@[equational_result]
theorem Equation428_implies_Equation835 (G : Type*) [Magma G] (h : Equation428 G) : Equation835 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq12


@[equational_result]
theorem Equation428_implies_Equation836 (G : Type*) [Magma G] (h : Equation428 G) : Equation836 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.2 in 12
  have eq33 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq32 eq15 -- backward demodulation 15,32
  subsumption eq33 eq12


@[equational_result]
theorem Equation4299_implies_Equation4288 (G : Type*) [Magma G] (h : Equation4299 G) : Equation4288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = (X3 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) = (X3 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq29 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK2)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq73 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ X0)) ≠ (X1 ◇ (sK2 ◇ sK2)) := superpose eq17 eq29 -- superposition 29,17, 17 into 29, unify on (0).2 in 17 and (0).1 in 29
  have eq278 (X0 X1 X3 X4 : G) : (X3 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X4)) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).2 in 15
  have eq311 (X1 X2 : G) : (X2 ◇ (sK2 ◇ sK2)) ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1)) := superpose eq15 eq73 -- superposition 73,15, 15 into 73, unify on (0).2 in 15 and (0).1 in 73
  subsumption eq311 eq278


@[equational_result]
theorem Equation4299_implies_Equation4297 (G : Type*) [Magma G] (h : Equation4299 G) : Equation4297 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = (X3 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) = (X3 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq29 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK2)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq73 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ X0)) ≠ (X1 ◇ (sK2 ◇ sK2)) := superpose eq17 eq29 -- superposition 29,17, 17 into 29, unify on (0).2 in 17 and (0).1 in 29
  have eq278 (X0 X1 X3 X4 : G) : (X3 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X4)) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).2 in 15
  have eq311 (X1 X2 : G) : (X2 ◇ (sK2 ◇ sK2)) ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1)) := superpose eq15 eq73 -- superposition 73,15, 15 into 73, unify on (0).2 in 15 and (0).1 in 73
  subsumption eq311 eq278


@[equational_result]
theorem Equation4299_implies_Equation4304 (G : Type*) [Magma G] (h : Equation4299 G) : Equation4304 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) = (X3 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X1 ◇ (sK1 ◇ sK1)) := superpose eq9 eq18 -- superposition 18,9, 9 into 18, unify on (0).2 in 9 and (0).2 in 18
  have eq128 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq17 eq21 -- superposition 21,17, 17 into 21, unify on (0).2 in 17 and (0).1 in 21
  have eq280 (X0 X1 X3 X4 : G) : (X3 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X4)) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).2 in 15
  have eq313 (X1 X2 : G) : (X2 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1)) := superpose eq15 eq128 -- superposition 128,15, 15 into 128, unify on (0).2 in 15 and (0).2 in 128
  subsumption eq313 eq280


@[equational_result]
theorem Equation4299_implies_Equation4308 (G : Type*) [Magma G] (h : Equation4299 G) : Equation4308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) = (X3 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq74 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK2)) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq17 eq18 -- superposition 18,17, 17 into 18, unify on (0).2 in 17 and (0).1 in 18
  have eq271 (X0 X1 X3 X4 : G) : (X3 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X4)) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).2 in 15
  have eq331 (X1 X2 : G) : (X2 ◇ (sK2 ◇ sK2)) ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1)) := superpose eq15 eq74 -- superposition 74,15, 15 into 74, unify on (0).2 in 15 and (0).2 in 74
  subsumption eq331 eq271


@[equational_result]
theorem Equation4299_implies_Equation4312 (G : Type*) [Magma G] (h : Equation4299 G) : Equation4312 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = (X3 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) = (X3 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq29 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK3 ◇ sK3)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq73 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ X0)) ≠ (X1 ◇ (sK3 ◇ sK3)) := superpose eq17 eq29 -- superposition 29,17, 17 into 29, unify on (0).2 in 17 and (0).1 in 29
  have eq278 (X0 X1 X3 X4 : G) : (X3 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X4)) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).2 in 15
  have eq311 (X1 X2 : G) : (X2 ◇ (sK3 ◇ sK3)) ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1)) := superpose eq15 eq73 -- superposition 73,15, 15 into 73, unify on (0).2 in 15 and (0).1 in 73
  subsumption eq311 eq278


@[equational_result]
theorem Equation4299_implies_Equation4355 (G : Type*) [Magma G] (h : Equation4299 G) : Equation4355 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = (X3 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) = (X3 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq29 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK3 ◇ sK3)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq75 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK3 ◇ (sK3 ◇ X0)) := superpose eq17 eq29 -- superposition 29,17, 17 into 29, unify on (0).2 in 17 and (0).2 in 29
  have eq269 (X0 X1 X3 X4 : G) : (X3 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X4)) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).2 in 15
  have eq302 (X1 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X1)) := superpose eq15 eq75 -- superposition 75,15, 15 into 75, unify on (0).2 in 15 and (0).2 in 75
  subsumption eq302 eq269


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
theorem Equation433_implies_Equation1067 (G : Type*) [Magma G] (h : Equation433 G) : Equation1067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation433_implies_Equation854 (G : Type*) [Magma G] (h : Equation433 G) : Equation854 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2.2 in 9
  have eq74 : sK0 ≠ sK0 := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq74 rfl


@[equational_result]
theorem Equation434_implies_Equation1060 (G : Type*) [Magma G] (h : Equation434 G) : Equation1060 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2 in 13
  subsumption eq17 rfl


@[equational_result]
theorem Equation434_implies_Equation1855 (G : Type*) [Magma G] (h : Equation434 G) : Equation1855 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2 in 13
  subsumption eq17 rfl


@[equational_result]
theorem Equation434_implies_Equation1863 (G : Type*) [Magma G] (h : Equation434 G) : Equation1863 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq11


@[equational_result]
theorem Equation434_implies_Equation360 (G : Type*) [Magma G] (h : Equation434 G) : Equation360 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq23 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq23 rfl


@[equational_result]
theorem Equation434_implies_Equation443 (G : Type*) [Magma G] (h : Equation434 G) : Equation443 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2 in 13
  subsumption eq17 rfl


@[equational_result]
theorem Equation434_implies_Equation840 (G : Type*) [Magma G] (h : Equation434 G) : Equation840 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq11


@[equational_result]
theorem Equation438_implies_Equation462 (G : Type*) [Magma G] (h : Equation438 G) : Equation462 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq13 eq12 -- backward demodulation 12,13
  have eq17 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation439_implies_Equation359 (G : Type*) [Magma G] (h : Equation439 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq14 rfl


@[equational_result]
theorem Equation4407_implies_Equation4431 (G : Type*) [Magma G] (h : Equation4407 G) : Equation4431 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ sK4) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq31 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq67 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X4) = (X3 ◇ (X3 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq183 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq16 eq31 -- superposition 31,16, 16 into 31, unify on (0).2 in 16 and (0).2 in 31
  subsumption eq183 eq67


@[equational_result]
theorem Equation4411_implies_Equation4427 (G : Type*) [Magma G] (h : Equation4411 G) : Equation4427 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X0 ◇ X4) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq33 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ X0) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  have eq138 (X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (((X1 ◇ X2) ◇ sK2) ◇ sK0) := superpose eq17 eq33 -- superposition 33,17, 17 into 33, unify on (0).2 in 17 and (0).2 in 33
  subsumption eq138 eq68


@[equational_result]
theorem Equation441_implies_Equation4 (G : Type*) [Magma G] (h : Equation441 G) : Equation4 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ sK1) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation441_implies_Equation649 (G : Type*) [Magma G] (h : Equation441 G) : Equation649 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation4417_implies_Equation4429 (G : Type*) [Magma G] (h : Equation4417 G) : Equation4429 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK3 ◇ (sK3 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq19 (X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ sK3) ◇ X1) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq44 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ X3)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq250 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = ((X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq274 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ ((sK3 ◇ (sK3 ◇ X0)) ◇ sK3)) ◇ X1) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).2 in 19
  have eq358 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = ((X0 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) := superpose eq44 eq13 -- superposition 13,44, 44 into 13, unify on (0).2 in 44 and (0).1.1 in 13
  have eq8557 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ ((sK3 ◇ X0) ◇ X2)) ◇ X1) := superpose eq358 eq274 -- superposition 274,358, 358 into 274, unify on (0).2 in 358 and (0).2 in 274
  have eq8685 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq44 eq8557 -- superposition 8557,44, 44 into 8557, unify on (0).2 in 44 and (0).2.1 in 8557
  have eq8936 (X0 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (X0 ◇ X2)) := superpose eq250 eq8685 -- superposition 8685,250, 250 into 8685, unify on (0).2 in 250 and (0).2 in 8685
  subsumption eq8936 rfl


@[equational_result]
theorem Equation4419_implies_Equation4411 (G : Type*) [Magma G] (h : Equation4419 G) : Equation4411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X0) = ((X3 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (((X2 ◇ X1) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X2)) = ((X2 ◇ (X2 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq20 (X1 X2 X3 X4 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ X3) = ((X4 ◇ X2) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq33 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X0 ◇ sK2) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq69 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq187 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq20 eq11 -- superposition 11,20, 20 into 11, unify on (0).2 in 20 and (0).2.2 in 11
  have eq188 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).2.2 in 11
  have eq395 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  have eq430 (X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ (sK2 ◇ X1))) := superpose eq14 eq33 -- superposition 33,14, 14 into 33, unify on (0).2 in 14 and (0).2 in 33
  have eq458 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq9 eq395 -- forward demodulation 395,9
  have eq459 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ X1)) := superpose eq69 eq458 -- forward demodulation 458,69
  have eq460 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = ((X3 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq459 eq188 -- backward demodulation 188,459
  have eq463 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq460 eq187 -- backward demodulation 187,460
  have eq466 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq463 eq11 -- backward demodulation 11,463
  have eq564 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose eq15 eq466 -- superposition 466,15, 15 into 466, unify on (0).2 in 15 and (0).2 in 466
  have eq600 (X1 : G) : (sK0 ◇ (sK0 ◇ (sK2 ◇ X1))) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq564 eq430 -- backward demodulation 430,564
  subsumption eq600 eq564


@[equational_result]
theorem Equation442_implies_Equation432 (G : Type*) [Magma G] (h : Equation442 G) : Equation432 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X3 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq40 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X0)) = ((X3 ◇ (X3 ◇ X0)) ◇ (X4 ◇ (X4 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq218 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq9 eq40 -- superposition 40,9, 9 into 40, unify on (0).2 in 9 and (0).2.2 in 40
  have eq255 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq9 eq218 -- superposition 218,9, 9 into 218, unify on (0).2 in 9 and (0).1 in 218
  have eq417 : sK0 ≠ sK0 := superpose eq255 eq10 -- superposition 10,255, 255 into 10, unify on (0).2 in 255 and (0).2 in 10
  subsumption eq417 rfl


@[equational_result]
theorem Equation4444_implies_Equation4465 (G : Type*) [Magma G] (h : Equation4444 G) : Equation4465 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK3) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq30 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK3) ◇ X0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq107 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq115 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq17 eq30 -- superposition 30,17, 17 into 30, unify on (0).2 in 17 and (0).2 in 30
  subsumption eq115 eq107


@[equational_result]
theorem Equation4448_implies_Equation4391 (G : Type*) [Magma G] (h : Equation4448 G) : Equation4391 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK1 ◇ sK2) ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X0 ◇ X4) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq33 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ X0) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).1 in 10
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  have eq138 (X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (((X1 ◇ X2) ◇ sK1) ◇ sK0) := superpose eq17 eq33 -- superposition 33,17, 17 into 33, unify on (0).2 in 17 and (0).2 in 33
  subsumption eq138 eq68


@[equational_result]
theorem Equation4448_implies_Equation4438 (G : Type*) [Magma G] (h : Equation4448 G) : Equation4438 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq63 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2 in 15
  have eq270 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X3)) = (X3 ◇ (X5 ◇ X3)) := superpose eq63 eq63 -- superposition 63,63, 63 into 63, unify on (0).2 in 63 and (0).2 in 63
  have eq510 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq270 eq11 -- superposition 11,270, 270 into 11, unify on (0).2 in 270 and (0).1 in 11
  subsumption eq510 eq270


@[equational_result]
theorem Equation4448_implies_Equation4452 (G : Type*) [Magma G] (h : Equation4448 G) : Equation4452 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X0 ◇ X4) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq37 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ X0) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  have eq151 (X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (((X1 ◇ X2) ◇ sK2) ◇ sK0) := superpose eq17 eq37 -- superposition 37,17, 17 into 37, unify on (0).2 in 17 and (0).2 in 37
  subsumption eq151 eq68


@[equational_result]
theorem Equation4448_implies_Equation4456 (G : Type*) [Magma G] (h : Equation4448 G) : Equation4456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X0 ◇ X4) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq33 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ X0) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  have eq138 (X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (((X1 ◇ X2) ◇ sK2) ◇ sK0) := superpose eq17 eq33 -- superposition 33,17, 17 into 33, unify on (0).2 in 17 and (0).2 in 33
  subsumption eq138 eq68


@[equational_result]
theorem Equation4448_implies_Equation4460 (G : Type*) [Magma G] (h : Equation4448 G) : Equation4460 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X0 ◇ X4) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq33 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ X0) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  have eq138 (X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (((X1 ◇ X2) ◇ sK2) ◇ sK0) := superpose eq17 eq33 -- superposition 33,17, 17 into 33, unify on (0).2 in 17 and (0).2 in 33
  subsumption eq138 eq68


@[equational_result]
theorem Equation4448_implies_Equation4464 (G : Type*) [Magma G] (h : Equation4448 G) : Equation4464 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK3) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X0 ◇ X4) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq33 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ X0) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  have eq138 (X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (((X1 ◇ X2) ◇ sK2) ◇ sK0) := superpose eq17 eq33 -- superposition 33,17, 17 into 33, unify on (0).2 in 17 and (0).2 in 33
  subsumption eq138 eq68


@[equational_result]
theorem Equation444_implies_Equation858 (G : Type*) [Magma G] (h : Equation444 G) : Equation858 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq16 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq16 rfl


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
theorem Equation4453_implies_Equation4465 (G : Type*) [Magma G] (h : Equation4453 G) : Equation4465 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK3) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X1) = ((X3 ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = ((X1 ◇ (X2 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq34 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((X0 ◇ sK3) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq66 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) = ((X2 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2.1.2 in 15
  have eq73 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = ((X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2.1 in 15
  have eq74 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = ((X3 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).2 in 15
  have eq77 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) = ((X3 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq95 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3) := superpose eq74 eq73 -- backward demodulation 73,74
  have eq98 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) = (X1 ◇ (X3 ◇ X1)) := superpose eq74 eq66 -- backward demodulation 66,74
  have eq100 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) = (X0 ◇ (X2 ◇ X0)) := superpose eq74 eq77 -- forward demodulation 77,74
  have eq101 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq74 eq100 -- forward demodulation 100,74
  have eq206 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X2) = (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq270 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq98 eq206 -- forward demodulation 206,98
  have eq501 (X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (((X1 ◇ sK3) ◇ ((X2 ◇ sK3) ◇ X1)) ◇ sK1) := superpose eq11 eq34 -- superposition 34,11, 11 into 34, unify on (0).2 in 11 and (0).2.1 in 34
  have eq563 (X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK3 ◇ (((X2 ◇ sK3) ◇ X1) ◇ sK3)) ◇ sK1) := superpose eq9 eq501 -- forward demodulation 501,9
  have eq564 (X1 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK3 ◇ ((sK3 ◇ (X1 ◇ sK3)) ◇ sK3)) ◇ sK1) := superpose eq9 eq563 -- forward demodulation 563,9
  have eq565 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK3 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ sK3)))) ◇ sK1) := superpose eq270 eq564 -- forward demodulation 564,270
  have eq606 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1)))) := superpose eq101 eq101 -- superposition 101,101, 101 into 101, unify on (0).2 in 101 and (0).2.2.2 in 101
  have eq723 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) = ((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq270 eq606 -- forward demodulation 606,270
  have eq724 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq270 eq723 -- forward demodulation 723,270
  have eq725 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK3 ◇ (sK3 ◇ (sK3 ◇ sK3))) ◇ sK1) := superpose eq724 eq565 -- backward demodulation 565,724
  subsumption eq725 eq95


@[equational_result]
theorem Equation4454_implies_Equation4466 (G : Type*) [Magma G] (h : Equation4454 G) : Equation4466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK3 ◇ (X0 ◇ sK3)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq19 (X1 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((X1 ◇ sK3) ◇ X1) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq36 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = (((X2 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2.1 in 9
  have eq94 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ X3) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2.2 in 12
  have eq128 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (((X1 ◇ X0) ◇ X1) ◇ (sK3 ◇ X0)) := superpose eq13 eq19 -- superposition 19,13, 13 into 19, unify on (0).2 in 13 and (0).2.1 in 19
  have eq2737 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X3)) = ((X5 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0)) ◇ X5) := superpose eq36 eq94 -- superposition 94,36, 36 into 94, unify on (0).2 in 36 and (0).2 in 94
  have eq3939 (X0 X1 X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0)) ◇ X3) := superpose eq94 eq128 -- superposition 128,94, 94 into 128, unify on (0).2 in 94 and (0).2 in 128
  subsumption eq3939 eq2737


@[equational_result]
theorem Equation445_implies_Equation636 (G : Type*) [Magma G] (h : Equation445 G) : Equation636 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK2) ◇ sK1))) := mod_symm nh
  have eq13 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq13


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
  have eq10950 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq114 eq158 -- superposition 158,114, 114 into 158, unify on (0).2 in 114 and (0).2 in 158
  have eq11051 (X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2)) = (X4 ◇ (X5 ◇ (X4 ◇ X5))) := superpose eq11 eq10950 -- superposition 10950,11, 11 into 10950, unify on (0).2 in 11 and (0).1 in 10950
  have eq11212 (X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) ≠ ((X3 ◇ sK2) ◇ ((X4 ◇ X3) ◇ X3)) := superpose eq10950 eq444 -- superposition 444,10950, 10950 into 444, unify on (0).2 in 10950 and (0).2 in 444
  subsumption eq11212 eq11051


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
theorem Equation4481_implies_Equation4505 (G : Type*) [Magma G] (h : Equation4481 G) : Equation4505 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ sK4) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq33 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq69 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X5) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  have eq357 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((((sK2 ◇ sK3) ◇ X0) ◇ X1) ◇ X2) := superpose eq68 eq33 -- superposition 33,68, 68 into 33, unify on (0).2 in 68 and (0).2 in 33
  subsumption eq357 eq69


@[equational_result]
theorem Equation448_implies_Equation441 (G : Type*) [Magma G] (h : Equation448 G) : Equation441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation4485_implies_Equation4501 (G : Type*) [Magma G] (h : Equation4485 G) : Equation4501 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq73 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).2 in 15
  have eq307 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X4)) = (X3 ◇ (X5 ◇ X5)) := superpose eq73 eq73 -- superposition 73,73, 73 into 73, unify on (0).2 in 73 and (0).2 in 73
  have eq606 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq307 eq18 -- superposition 18,307, 307 into 18, unify on (0).2 in 307 and (0).2 in 18
  subsumption eq606 eq307


@[equational_result]
theorem Equation4493_implies_Equation4485 (G : Type*) [Magma G] (h : Equation4493 G) : Equation4485 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK1 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ X2) = (X2 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X0) = ((X3 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X2)) = ((X2 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq35 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((X0 ◇ sK2) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq75 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = ((X3 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq13 eq16 -- superposition 16,13, 13 into 16, unify on (0).2 in 13 and (0).2 in 16
  have eq285 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X3)) = ((X4 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) ◇ X2) := superpose eq9 eq75 -- superposition 75,9, 9 into 75, unify on (0).2 in 9 and (0).2.1.2 in 75
  have eq481 (X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X1))) ◇ sK0) := superpose eq11 eq35 -- superposition 35,11, 11 into 35, unify on (0).2 in 11 and (0).2.1 in 35
  subsumption eq481 eq285


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
  have eq7644 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2))))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2)))))))) = X2 := superpose eq429 eq9 -- superposition 9,429, 429 into 9, unify on (0).2 in 429 and (0).1.2 in 9
  have eq7667 (X0 X1 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X0 ◇ (X3 ◇ X0)) ◇ (X4 ◇ (X0 ◇ (X3 ◇ X0))))) := superpose eq16 eq7644 -- superposition 7644,16, 16 into 7644, unify on (0).2 in 16 and (0).1.2.1.2.2 in 7644
  have eq7715 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7667 eq9 -- superposition 9,7667, 7667 into 9, unify on (0).2 in 7667 and (0).1.2 in 9
  have eq8349 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq7715 eq9 -- superposition 9,7715, 7715 into 9, unify on (0).2 in 7715 and (0).1.2.2 in 9
  have eq8511 : sK0 ≠ sK0 := superpose eq8349 eq10 -- superposition 10,8349, 8349 into 10, unify on (0).2 in 8349 and (0).2 in 10
  subsumption eq8511 rfl


