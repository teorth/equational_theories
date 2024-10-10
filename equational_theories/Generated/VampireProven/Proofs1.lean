import equational_theories.Superposition
import equational_theories.Equations.All
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation102_implies_Equation1029 (G : Type*) [Magma G] (h : Equation102 G) : Equation1029 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq9


@[equational_result]
theorem Equation102_implies_Equation1226 (G : Type*) [Magma G] (h : Equation102 G) : Equation1226 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq9


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
theorem Equation102_implies_Equation1632 (G : Type*) [Magma G] (h : Equation102 G) : Equation1632 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq9


@[equational_result]
theorem Equation102_implies_Equation2449 (G : Type*) [Magma G] (h : Equation102 G) : Equation2449 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 : sK0 ≠ (sK0 ◇ sK0) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : sK0 ≠ sK0 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).2 in 11
  subsumption eq14 rfl


@[equational_result]
theorem Equation102_implies_Equation3 (G : Type*) [Magma G] (h : Equation102 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation102_implies_Equation3459 (G : Type*) [Magma G] (h : Equation102 G) : Equation3459 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq11 : sK0 ≠ (sK0 ◇ sK0) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : sK0 ≠ sK0 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).2 in 11
  subsumption eq14 rfl


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
theorem Equation102_implies_Equation617 (G : Type*) [Magma G] (h : Equation102 G) : Equation617 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := mod_symm nh
  have eq11 : sK0 ≠ (sK0 ◇ sK0) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : sK0 ≠ sK0 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).2 in 11
  subsumption eq14 rfl


@[equational_result]
theorem Equation1027_implies_Equation628 (G : Type*) [Magma G] (h : Equation1027 G) : Equation628 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK3))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation102_implies_Equation826 (G : Type*) [Magma G] (h : Equation102 G) : Equation826 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq9


@[equational_result]
theorem Equation1030_implies_Equation831 (G : Type*) [Magma G] (h : Equation1030 G) : Equation831 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq17 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq23 : sK0 ≠ sK0 := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq23 rfl


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
theorem Equation1042_implies_Equation105 (G : Type*) [Magma G] (h : Equation1042 G) : Equation105 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation1042_implies_Equation844 (G : Type*) [Magma G] (h : Equation1042 G) : Equation844 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq125 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.2 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.2.1 in 20
  have eq197 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq15 eq148 -- superposition 148,15, 15 into 148, unify on (0).2 in 15 and (0).2.2 in 148
  have eq515 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X1 := superpose eq197 eq9 -- superposition 9,197, 197 into 9, unify on (0).2 in 197 and (0).1.2 in 9
  have eq920 : sK0 ≠ sK0 := superpose eq515 eq10 -- superposition 10,515, 515 into 10, unify on (0).2 in 515 and (0).2 in 10
  subsumption eq920 rfl


@[equational_result]
theorem Equation1043_implies_Equation1053 (G : Type*) [Magma G] (h : Equation1043 G) : Equation1053 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2.1 in 11
  have eq21 (X0 X1 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq51 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) = (((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.2.1 in 21
  have eq55 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.2 in 11
  have eq64 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) = (((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) ◇ X0) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.2.1 in 21
  have eq70 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq55 eq11 -- superposition 11,55, 55 into 11, unify on (0).2 in 55 and (0).1.2.2.1 in 11
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.2.1.2 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq341 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.2.1 in 9
  have eq364 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq68 eq341 -- forward demodulation 341,68
  have eq380 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq364 eq70 -- backward demodulation 70,364
  have eq1466 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X1)) = ((X2 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X1))) := superpose eq64 eq9 -- superposition 9,64, 64 into 9, unify on (0).2 in 64 and (0).1.2 in 9
  have eq1543 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) = X2 := superpose eq364 eq1466 -- forward demodulation 1466,364
  have eq1606 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq1543 eq9 -- superposition 9,1543, 1543 into 9, unify on (0).2 in 1543 and (0).1.2.1 in 9
  have eq2625 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq1606 eq380 -- superposition 380,1606, 1606 into 380, unify on (0).2 in 1606 and (0).1.2 in 380
  have eq5365 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = X2 := superpose eq2625 eq9 -- superposition 9,2625, 2625 into 9, unify on (0).2 in 2625 and (0).1.2.1 in 9
  have eq5933 : sK0 ≠ sK0 := superpose eq5365 eq10 -- superposition 10,5365, 5365 into 10, unify on (0).2 in 5365 and (0).2 in 10
  subsumption eq5933 rfl


@[equational_result]
theorem Equation1043_implies_Equation433 (G : Type*) [Magma G] (h : Equation1043 G) : Equation433 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2.1 in 11
  have eq21 (X0 X1 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq51 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) = (((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.2.1 in 21
  have eq55 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.2 in 11
  have eq64 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) = (((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) ◇ X0) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.2.1 in 21
  have eq70 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq55 eq11 -- superposition 11,55, 55 into 11, unify on (0).2 in 55 and (0).1.2.2.1 in 11
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.2.1.2 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq341 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.2.1 in 9
  have eq364 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq68 eq341 -- forward demodulation 341,68
  have eq380 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq364 eq70 -- backward demodulation 70,364
  have eq1467 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X1)) = ((X2 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X1))) := superpose eq64 eq9 -- superposition 9,64, 64 into 9, unify on (0).2 in 64 and (0).1.2 in 9
  have eq1544 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) = X2 := superpose eq364 eq1467 -- forward demodulation 1467,364
  have eq1567 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq380 eq1544 -- superposition 1544,380, 380 into 1544, unify on (0).2 in 380 and (0).1.2.1 in 1544
  have eq1954 : sK0 ≠ sK0 := superpose eq1567 eq10 -- superposition 10,1567, 1567 into 10, unify on (0).2 in 1567 and (0).2 in 10
  subsumption eq1954 rfl


@[equational_result]
theorem Equation1043_implies_Equation434 (G : Type*) [Magma G] (h : Equation1043 G) : Equation434 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2.1 in 11
  have eq21 (X0 X1 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq55 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.2 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.2.1 in 21
  have eq70 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq55 eq11 -- superposition 11,55, 55 into 11, unify on (0).2 in 55 and (0).1.2.2.1 in 11
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.2.1.2 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq341 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.2.1 in 9
  have eq364 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq68 eq341 -- forward demodulation 341,68
  have eq380 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq364 eq70 -- backward demodulation 70,364
  have eq392 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq364 eq10 -- backward demodulation 10,364
  subsumption eq392 eq380


@[equational_result]
theorem Equation1043_implies_Equation442 (G : Type*) [Magma G] (h : Equation1043 G) : Equation442 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2.1 in 11
  have eq21 (X0 X1 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq51 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) = (((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.2.1 in 21
  have eq55 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.2 in 11
  have eq64 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) = (((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) ◇ X0) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.2.1 in 21
  have eq70 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq55 eq11 -- superposition 11,55, 55 into 11, unify on (0).2 in 55 and (0).1.2.2.1 in 11
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.2.1.2 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq341 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.2.1 in 9
  have eq364 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq68 eq341 -- forward demodulation 341,68
  have eq380 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq364 eq70 -- backward demodulation 70,364
  have eq1467 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X1)) = ((X2 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X1))) := superpose eq64 eq9 -- superposition 9,64, 64 into 9, unify on (0).2 in 64 and (0).1.2 in 9
  have eq1544 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) = X2 := superpose eq364 eq1467 -- forward demodulation 1467,364
  have eq1567 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq380 eq1544 -- superposition 1544,380, 380 into 1544, unify on (0).2 in 380 and (0).1.2.1 in 1544
  have eq1901 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X1)))) = X1 := superpose eq1567 eq9 -- superposition 9,1567, 1567 into 9, unify on (0).2 in 1567 and (0).1.2.1 in 9
  have eq2348 : sK0 ≠ sK0 := superpose eq1901 eq10 -- superposition 10,1901, 1901 into 10, unify on (0).2 in 1901 and (0).2 in 10
  subsumption eq2348 rfl


@[equational_result]
theorem Equation1043_implies_Equation838 (G : Type*) [Magma G] (h : Equation1043 G) : Equation838 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2.1 in 11
  have eq21 (X0 X1 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq55 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.2 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.2.1 in 21
  have eq75 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq55 eq11 -- superposition 11,55, 55 into 11, unify on (0).2 in 55 and (0).1.2.2.1.2 in 11
  have eq131 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.2.1.2 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq12 eq131 -- forward demodulation 131,12
  have eq341 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.2.1 in 9
  have eq364 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq68 eq341 -- forward demodulation 341,68
  have eq381 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) = X0 := superpose eq364 eq75 -- backward demodulation 75,364
  have eq1079 : sK0 ≠ sK0 := superpose eq381 eq10 -- superposition 10,381, 381 into 10, unify on (0).2 in 381 and (0).2 in 10
  subsumption eq1079 rfl


@[equational_result]
theorem Equation1047_implies_Equation650 (G : Type*) [Magma G] (h : Equation1047 G) : Equation650 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq35 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.2.2 in 12
  have eq39 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.2 in 12
  have eq70 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq82 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq70 eq9 -- backward demodulation 9,70
  have eq83 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq70 eq12 -- backward demodulation 12,70
  have eq87 : sK0 ≠ (sK0 ◇ sK1) := superpose eq82 eq10 -- backward demodulation 10,82
  have eq90 : sK0 ≠ sK0 := superpose eq83 eq87 -- superposition 87,83, 83 into 87, unify on (0).2 in 83 and (0).2 in 87
  subsumption eq90 rfl


@[equational_result]
theorem Equation1050_implies_Equation56 (G : Type*) [Magma G] (h : Equation1050 G) : Equation56 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation1051_implies_Equation107 (G : Type*) [Magma G] (h : Equation1051 G) : Equation107 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation1052_implies_Equation108 (G : Type*) [Magma G] (h : Equation1052 G) : Equation108 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1052_implies_Equation846 (G : Type*) [Magma G] (h : Equation1052 G) : Equation846 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq18 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq49 : sK0 ≠ sK0 := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq49 rfl


@[equational_result]
theorem Equation1056_implies_Equation444 (G : Type*) [Magma G] (h : Equation1056 G) : Equation444 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation1056_implies_Equation848 (G : Type*) [Magma G] (h : Equation1056 G) : Equation848 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq47 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation1068_implies_Equation111 (G : Type*) [Magma G] (h : Equation1068 G) : Equation111 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq29 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation1068_implies_Equation1230 (G : Type*) [Magma G] (h : Equation1068 G) : Equation1230 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq128 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq128 rfl


@[equational_result]
theorem Equation1068_implies_Equation1243 (G : Type*) [Magma G] (h : Equation1068 G) : Equation1243 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq144 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq144 rfl


@[equational_result]
theorem Equation1068_implies_Equation1262 (G : Type*) [Magma G] (h : Equation1068 G) : Equation1262 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq144 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq144 rfl


@[equational_result]
theorem Equation1068_implies_Equation1263 (G : Type*) [Magma G] (h : Equation1068 G) : Equation1263 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq144 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq144 rfl


@[equational_result]
theorem Equation1068_implies_Equation1264 (G : Type*) [Magma G] (h : Equation1068 G) : Equation1264 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq144 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq144 rfl


@[equational_result]
theorem Equation1068_implies_Equation1265 (G : Type*) [Magma G] (h : Equation1068 G) : Equation1265 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK1) ◇ sK3)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq144 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq144 rfl


@[equational_result]
theorem Equation1077_implies_Equation2099 (G : Type*) [Magma G] (h : Equation1077 G) : Equation2099 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X1 X3 : G) : X1 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq19 (X0 : G) : sK0 ≠ (X0 ◇ (sK0 ◇ sK2)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq19 eq13


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
theorem Equation1087_implies_Equation944 (G : Type*) [Magma G] (h : Equation1087 G) : Equation944 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X1 X3 : G) : X1 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq19 (X0 : G) : sK0 ≠ (sK1 ◇ X0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq19 eq13


@[equational_result]
theorem Equation1088_implies_Equation1141 (G : Type*) [Magma G] (h : Equation1088 G) : Equation1141 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ ((X3 ◇ X1) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq13 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X0)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq21 : sK0 ≠ (sK1 ◇ (sK3 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq21 eq13


@[equational_result]
theorem Equation1088_implies_Equation2207 (G : Type*) [Magma G] (h : Equation1088 G) : Equation2207 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK2) ◇ (sK3 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ ((X3 ◇ X1) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq13 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X0)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq23 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq23 rfl


@[equational_result]
theorem Equation1096_implies_Equation1202 (G : Type*) [Magma G] (h : Equation1096 G) : Equation1202 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK3 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ ((X3 ◇ X1) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = (X0 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq16 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ ((X3 ◇ X1) ◇ X3)) = X3 := superpose eq13 eq11 -- backward demodulation 11,13
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X0) := superpose eq16 eq16 -- superposition 16,16, 16 into 16, unify on (0).2 in 16 and (0).1.2 in 16
  have eq26 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK3 ◇ sK1)) ◇ sK0)) := superpose eq22 eq10 -- backward demodulation 10,22
  have eq27 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq13 eq26 -- forward demodulation 26,13
  subsumption eq27 eq12


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
theorem Equation1102_implies_Equation484 (G : Type*) [Magma G] (h : Equation1102 G) : Equation484 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 (X1 X3 : G) : X1 = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq21 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ X0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.2.2 in 10
  subsumption eq21 eq14


@[equational_result]
theorem Equation1115_implies_Equation1772 (G : Type*) [Magma G] (h : Equation1115 G) : Equation1772 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ ((X3 ◇ X1) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq24 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 rfl


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
theorem Equation1125_implies_Equation2195 (G : Type*) [Magma G] (h : Equation1125 G) : Equation2195 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK2) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X0 ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X1 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq13 eq12 -- backward demodulation 12,13
  have eq21 (X0 X2 X3 : G) : (X0 ◇ X3) = (X2 ◇ X3) := superpose eq13 eq19 -- forward demodulation 19,13
  have eq30 (X0 : G) : sK0 ≠ (X0 ◇ (sK0 ◇ sK0)) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq30 eq13


@[equational_result]
theorem Equation1129_implies_Equation2178 (G : Type*) [Magma G] (h : Equation1129 G) : Equation2178 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation1133_implies_Equation1780 (G : Type*) [Magma G] (h : Equation1133 G) : Equation1780 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1133_implies_Equation1979 (G : Type*) [Magma G] (h : Equation1133 G) : Equation1979 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq34 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq34 eq12


@[equational_result]
theorem Equation1133_implies_Equation3935 (G : Type*) [Magma G] (h : Equation1133 G) : Equation3935 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq34 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq34 rfl


@[equational_result]
theorem Equation1141_implies_Equation169 (G : Type*) [Magma G] (h : Equation1141 G) : Equation169 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation114_implies_Equation1941 (G : Type*) [Magma G] (h : Equation114 G) : Equation1941 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X1 ◇ X0) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq22 : sK0 ≠ (sK2 ◇ (sK0 ◇ sK0)) := superpose eq18 eq10 -- backward demodulation 10,18
  subsumption eq22 eq18


@[equational_result]
theorem Equation1147_implies_Equation2974 (G : Type*) [Magma G] (h : Equation1147 G) : Equation2974 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X3) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq40 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq48 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq40 eq10 -- backward demodulation 10,40
  have eq52 (X1 X3 : G) : (X1 ◇ X1) = X3 := superpose eq12 eq40 -- superposition 40,12, 12 into 40, unify on (0).2 in 12 and (0).2 in 40
  have eq73 : sK0 ≠ (sK1 ◇ sK1) := superpose eq40 eq48 -- superposition 48,40, 40 into 48, unify on (0).2 in 40 and (0).2 in 48
  subsumption eq73 eq52


@[equational_result]
theorem Equation1148_implies_Equation1367 (G : Type*) [Magma G] (h : Equation1148 G) : Equation1367 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK1) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 X3 : G) : (X3 ◇ X1) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X2 X3 : G) : X2 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq19 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2.1 in 10
  subsumption eq19 eq13


@[equational_result]
theorem Equation1150_implies_Equation1763 (G : Type*) [Magma G] (h : Equation1150 G) : Equation1763 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X2 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq21 (X1 X2 X3 : G) : (X3 ◇ X1) = (X2 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2)) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq36 (X2 X3 : G) : (X3 ◇ (X3 ◇ X2)) = X2 := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).1 in 21
  have eq40 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2.2 in 21
  have eq41 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X2) = (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.2 in 21
  have eq56 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2)) = X2 := superpose eq40 eq26 -- backward demodulation 26,40
  have eq64 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X2) = ((X2 ◇ X1) ◇ X2) := superpose eq40 eq41 -- forward demodulation 41,40
  have eq313 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X2 ◇ X1) ◇ X0)) = X0 := superpose eq64 eq56 -- superposition 56,64, 64 into 56, unify on (0).2 in 64 and (0).1.2 in 56
  have eq327 (X0 : G) : sK0 ≠ ((sK1 ◇ sK2) ◇ ((X0 ◇ sK2) ◇ sK0)) := superpose eq64 eq10 -- superposition 10,64, 64 into 10, unify on (0).2 in 64 and (0).2.2 in 10
  have eq328 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ ((X2 ◇ X1) ◇ X0)) = X0 := superpose eq36 eq313 -- forward demodulation 313,36
  subsumption eq327 eq328


@[equational_result]
theorem Equation1151_implies_Equation689 (G : Type*) [Magma G] (h : Equation1151 G) : Equation689 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK2 ◇ sK0) ◇ sK3))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ ((X3 ◇ X2) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq24 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X2) = X0 := superpose eq16 eq11 -- backward demodulation 11,16
  have eq27 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = (((X3 ◇ X2) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq9 eq24 -- superposition 24,9, 9 into 24, unify on (0).2 in 9 and (0).1.1.1.2 in 24
  have eq34 (X1 X2 X3 : G) : ((X3 ◇ X2) ◇ X1) = X2 := superpose eq24 eq24 -- superposition 24,24, 24 into 24, unify on (0).2 in 24 and (0).1.1.1 in 24
  have eq37 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = X3 := superpose eq12 eq24 -- superposition 24,12, 12 into 24, unify on (0).2 in 12 and (0).1 in 24
  have eq43 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq16 eq27 -- forward demodulation 27,16
  have eq45 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq43 eq16 -- backward demodulation 16,43
  have eq51 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq45 eq10 -- backward demodulation 10,45
  have eq65 (X1 X3 : G) : X1 = X3 := superpose eq34 eq37 -- superposition 37,34, 34 into 37, unify on (0).2 in 34 and (0).1 in 37
  have eq75 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X1 ◇ X0)) := superpose eq37 eq51 -- superposition 51,37, 37 into 51, unify on (0).2 in 37 and (0).2 in 51
  subsumption eq75 eq65


@[equational_result]
theorem Equation1152_implies_Equation2576 (G : Type*) [Magma G] (h : Equation1152 G) : Equation2576 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK0) ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ ((X3 ◇ X2) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq18 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ (((X3 ◇ X1) ◇ X3) ◇ X5)) ◇ X4) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))) = X5 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq23 (X1 X3 X4 X5 : G) : (((X4 ◇ (((X3 ◇ X1) ◇ X3) ◇ X5)) ◇ X4) ◇ X1) = X5 := superpose eq9 eq18 -- forward demodulation 18,9
  have eq28 (X1 X2 X3 X4 : G) : ((X3 ◇ X1) ◇ X3) = (((X4 ◇ X2) ◇ X4) ◇ (X1 ◇ X2)) := superpose eq11 eq23 -- superposition 23,11, 11 into 23, unify on (0).2 in 11 and (0).1.1.1.2 in 23
  have eq62 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X4) = (((X5 ◇ (X2 ◇ X1)) ◇ X5) ◇ ((X3 ◇ X2) ◇ X3)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq101 (X0 X1 X4 : G) : ((X4 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X4) = X1 := superpose eq11 eq62 -- forward demodulation 62,11
  have eq271 : sK0 ≠ sK0 := superpose eq101 eq10 -- superposition 10,101, 101 into 10, unify on (0).2 in 101 and (0).2 in 10
  subsumption eq271 rfl


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


@[equational_result]
theorem Equation1156_implies_Equation2110 (G : Type*) [Magma G] (h : Equation1156 G) : Equation2110 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK2) ◇ (sK0 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X2) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X2 X3 : G) : X2 = X3 := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1 in 14
  have eq21 (X0 : G) : sK0 ≠ (X0 ◇ (sK0 ◇ sK3)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.1 in 10
  subsumption eq21 eq15


@[equational_result]
theorem Equation1163_implies_Equation1378 (G : Type*) [Magma G] (h : Equation1163 G) : Equation1378 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK1) ◇ sK3) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X2) = (X0 ◇ ((X3 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X2) ◇ (X2 ◇ X2))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1.2 in 9
  have eq21 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X5 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2)))) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2))) = (X5 ◇ (((X3 ◇ (X0 ◇ X2)) ◇ X2) ◇ ((X4 ◇ (X5 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2)))) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.1 in 11
  have eq22 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = (X0 ◇ ((X4 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) ◇ ((X3 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq23 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ (X2 ◇ X2)) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X4 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X2) ◇ (X2 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.2 in 11
  have eq33 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X2)) = ((X3 ◇ X2) ◇ (X2 ◇ X2)) := superpose eq18 eq23 -- forward demodulation 23,18
  have eq34 (X2 X3 : G) : ((X3 ◇ X2) ◇ (X2 ◇ X2)) = X2 := superpose eq12 eq33 -- forward demodulation 33,12
  have eq35 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq34 eq18 -- backward demodulation 18,34
  have eq37 (X0 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ (X2 ◇ X2)) = (X0 ◇ ((X4 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X2) ◇ (X2 ◇ X2)))) := superpose eq35 eq22 -- backward demodulation 22,35
  have eq38 (X1 X2 X4 X5 : G) : ((X4 ◇ (X5 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2))) = (X5 ◇ ((X2 ◇ X2) ◇ ((X4 ◇ (X5 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2))))) := superpose eq35 eq21 -- backward demodulation 21,35
  have eq44 (X0 X2 X4 : G) : (X0 ◇ ((X4 ◇ (X2 ◇ X2)) ◇ X2)) = X2 := superpose eq34 eq37 -- forward demodulation 37,34
  have eq45 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X2 := superpose eq35 eq44 -- forward demodulation 44,35
  have eq46 (X1 X2 X5 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2))) = (X5 ◇ ((X2 ◇ X2) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2))))) := superpose eq35 eq38 -- forward demodulation 38,35
  have eq47 (X1 X2 X5 : G) : (X5 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2))) = (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2))) := superpose eq45 eq46 -- forward demodulation 46,45
  have eq48 (X2 X5 : G) : (X2 ◇ X2) = (X5 ◇ X2) := superpose eq45 eq47 -- forward demodulation 47,45
  have eq49 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq48 eq10 -- backward demodulation 10,48
  subsumption eq49 eq45


@[equational_result]
theorem Equation1167_implies_Equation2000 (G : Type*) [Magma G] (h : Equation1167 G) : Equation2000 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) = X2 := superpose eq18 eq11 -- backward demodulation 11,18
  have eq27 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq27 rfl


@[equational_result]
theorem Equation1167_implies_Equation3989 (G : Type*) [Magma G] (h : Equation1167 G) : Equation3989 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq65 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq65 rfl


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
theorem Equation1184_implies_Equation1949 (G : Type*) [Magma G] (h : Equation1184 G) : Equation1949 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq36 (X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X3)) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq69 : sK0 ≠ sK0 := superpose eq36 eq10 -- superposition 10,36, 36 into 10, unify on (0).2 in 36 and (0).2 in 10
  subsumption eq69 rfl


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
theorem Equation1202_implies_Equation1912 (G : Type*) [Magma G] (h : Equation1202 G) : Equation1912 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X3 X4 : G) : (X3 ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq35 : sK0 ≠ (sK2 ◇ (sK2 ◇ sK0)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq35 eq12


@[equational_result]
theorem Equation1233_implies_Equation102 (G : Type*) [Magma G] (h : Equation1233 G) : Equation102 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation1233_implies_Equation1024 (G : Type*) [Magma G] (h : Equation1233 G) : Equation1024 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq13 (X0 X3 : G) : (X0 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK2)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


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
theorem Equation1236_implies_Equation102 (G : Type*) [Magma G] (h : Equation1236 G) : Equation102 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ ((X0 ◇ X3) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq22 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation1236_implies_Equation1024 (G : Type*) [Magma G] (h : Equation1236 G) : Equation1024 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK2)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation1237_implies_Equation1034 (G : Type*) [Magma G] (h : Equation1237 G) : Equation1034 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK3)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ ((X0 ◇ X4) ◇ X5)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


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
theorem Equation124_implies_Equation1223 (G : Type*) [Magma G] (h : Equation124 G) : Equation1223 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2 in 10
  have eq15 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := superpose eq13 eq9 -- backward demodulation 9,13
  subsumption eq15 eq8


@[equational_result]
theorem Equation124_implies_Equation151 (G : Type*) [Magma G] (h : Equation124 G) : Equation151 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2 in 10
  have eq18 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.2.1 in 8
  have eq19 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq18 -- forward demodulation 18,13
  have eq36 : sK0 ≠ sK0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2 in 9
  subsumption eq36 rfl


@[equational_result]
theorem Equation124_implies_Equation1629 (G : Type*) [Magma G] (h : Equation124 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2 in 10
  have eq15 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq13 eq9 -- backward demodulation 9,13
  have eq19 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.2.1 in 8
  have eq20 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq19 -- forward demodulation 19,13
  have eq52 : sK0 ≠ sK0 := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq52 rfl


@[equational_result]
theorem Equation124_implies_Equation2035 (G : Type*) [Magma G] (h : Equation124 G) : Equation2035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2 in 10
  have eq15 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq13 eq9 -- backward demodulation 9,13
  have eq19 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.2.1 in 8
  have eq20 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq19 -- forward demodulation 19,13
  have eq52 : sK0 ≠ sK0 := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq52 rfl


@[equational_result]
theorem Equation1243_implies_Equation1251 (G : Type*) [Magma G] (h : Equation1243 G) : Equation1251 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ X2) = ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X0 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq27 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) = X1 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq36 : sK0 ≠ sK0 := superpose eq27 eq10 -- superposition 10,27, 27 into 10, unify on (0).2 in 27 and (0).2 in 10
  subsumption eq36 rfl


@[equational_result]
theorem Equation124_implies_Equation359 (G : Type*) [Magma G] (h : Equation124 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2 in 10
  have eq19 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2 in 9
  subsumption eq19 rfl


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
theorem Equation1245_implies_Equation1249 (G : Type*) [Magma G] (h : Equation1245 G) : Equation1249 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ ((X0 ◇ X3) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq28 (X0 X1 X2 : G) : (X2 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ (X0 ◇ X1))) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq55 (X0 X3 : G) : (X3 ◇ (((X0 ◇ X0) ◇ X3) ◇ X0)) = X3 := superpose eq9 eq28 -- superposition 28,9, 9 into 28, unify on (0).2 in 9 and (0).1.2.1.1.1 in 28
  have eq83 : sK0 ≠ sK0 := superpose eq55 eq10 -- superposition 10,55, 55 into 10, unify on (0).2 in 55 and (0).2 in 10
  subsumption eq83 rfl


@[equational_result]
theorem Equation1246_implies_Equation106 (G : Type*) [Magma G] (h : Equation1246 G) : Equation106 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X3))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq15 eq9 -- backward demodulation 9,15
  have eq28 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq28 rfl


@[equational_result]
theorem Equation1246_implies_Equation1247 (G : Type*) [Magma G] (h : Equation1246 G) : Equation1247 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X3))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.1.1 in 9
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq15 eq9 -- backward demodulation 9,15
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq15 eq16 -- forward demodulation 16,15
  have eq51 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) = X0 := superpose eq20 eq22 -- superposition 22,20, 20 into 22, unify on (0).2 in 20 and (0).1 in 22
  have eq120 : sK0 ≠ sK0 := superpose eq51 eq10 -- superposition 10,51, 51 into 10, unify on (0).2 in 51 and (0).2 in 10
  subsumption eq120 rfl


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
theorem Equation124_implies_Equation8 (G : Type*) [Magma G] (h : Equation124 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2 in 10
  have eq16 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.2 in 8
  have eq20 : sK0 ≠ sK0 := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2 in 9
  subsumption eq20 rfl


@[equational_result]
theorem Equation125_implies_Equation229 (G : Type*) [Magma G] (h : Equation125 G) : Equation229 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq16 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq19 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := superpose eq11 eq16 -- forward demodulation 16,11
  subsumption eq19 eq12


@[equational_result]
theorem Equation1253_implies_Equation108 (G : Type*) [Magma G] (h : Equation1253 G) : Equation108 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation125_implies_Equation4435 (G : Type*) [Magma G] (h : Equation125 G) : Equation4435 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


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
theorem Equation125_implies_Equation73 (G : Type*) [Magma G] (h : Equation125 G) : Equation73 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq14 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq14 rfl


@[equational_result]
theorem Equation1257_implies_Equation851 (G : Type*) [Magma G] (h : Equation1257 G) : Equation851 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X0 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation1258_implies_Equation104 (G : Type*) [Magma G] (h : Equation1258 G) : Equation104 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ ((X0 ◇ X3) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation1260_implies_Equation839 (G : Type*) [Magma G] (h : Equation1260 G) : Equation839 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ (X0 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq15 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X4 ◇ X3) ◇ ((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)))) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.1.1 in 11
  have eq21 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X0) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq55 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = X1 := superpose eq21 eq9 -- superposition 9,21, 21 into 9, unify on (0).2 in 21 and (0).1.2 in 9
  have eq140 (X0 X1 X3 : G) : (X3 ◇ ((X1 ◇ X3) ◇ (X0 ◇ X1))) = X3 := superpose eq55 eq15 -- superposition 15,55, 55 into 15, unify on (0).2 in 55 and (0).1.2.2 in 15
  have eq603 : sK0 ≠ sK0 := superpose eq140 eq10 -- superposition 10,140, 140 into 10, unify on (0).2 in 140 and (0).2 in 10
  subsumption eq603 rfl


@[equational_result]
theorem Equation1261_implies_Equation1246 (G : Type*) [Magma G] (h : Equation1261 G) : Equation1246 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X0 ◇ X4) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq34 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq13 eq16 -- superposition 16,13, 13 into 16, unify on (0).2 in 13 and (0).1.2 in 16
  have eq43 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) := superpose eq34 eq10 -- backward demodulation 10,34
  subsumption eq43 eq11


@[equational_result]
theorem Equation1261_implies_Equation834 (G : Type*) [Magma G] (h : Equation1261 G) : Equation834 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X0 ◇ X4) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation1261_implies_Equation837 (G : Type*) [Magma G] (h : Equation1261 G) : Equation837 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X0 ◇ X4) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation1261_implies_Equation840 (G : Type*) [Magma G] (h : Equation1261 G) : Equation840 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X0 ◇ X4) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation1263_implies_Equation1253 (G : Type*) [Magma G] (h : Equation1263 G) : Equation1253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq20 (X0 X1 X2 : G) : (X2 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq25 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) = X2 := superpose eq11 eq20 -- forward demodulation 20,11
  have eq61 : sK0 ≠ sK0 := superpose eq25 eq10 -- superposition 10,25, 25 into 10, unify on (0).2 in 25 and (0).2 in 10
  subsumption eq61 rfl


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
theorem Equation1265_implies_Equation1068 (G : Type*) [Magma G] (h : Equation1265 G) : Equation1068 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ ((X0 ◇ X1) ◇ X0)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq32 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq32 rfl


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
theorem Equation1271_implies_Equation1265 (G : Type*) [Magma G] (h : Equation1271 G) : Equation1265 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK1) ◇ sK3)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X0 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq81 : sK0 ≠ sK0 := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq81 rfl


@[equational_result]
theorem Equation127_implies_Equation179 (G : Type*) [Magma G] (h : Equation127 G) : Equation179 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq23 : sK0 ≠ sK0 := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq23 rfl


@[equational_result]
theorem Equation1280_implies_Equation2771 (G : Type*) [Magma G] (h : Equation1280 G) : Equation2771 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X1 X3 : G) : X1 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq20 (X0 : G) : sK0 ≠ (X0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation1282_implies_Equation521 (G : Type*) [Magma G] (h : Equation1282 G) : Equation521 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 (X1 X3 : G) : X1 = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq26 (X0 X1 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2.2 in 10
  subsumption eq26 eq16


@[equational_result]
theorem Equation1287_implies_Equation468 (G : Type*) [Magma G] (h : Equation1287 G) : Equation468 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X1 X3 : G) : X1 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq20 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2.2 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation1289_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1289 G) : Equation1020 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq15 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq18 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1 in 8
  have eq20 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1.1 in 8
  have eq24 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq18 eq20 -- forward demodulation 20,18
  have eq27 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq24 eq9 -- backward demodulation 9,24
  have eq32 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq18 eq8 -- superposition 8,18, 18 into 8, unify on (0).2 in 18 and (0).1.2.1 in 8
  have eq36 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq24 eq32 -- forward demodulation 32,24
  have eq62 : sK0 ≠ sK0 := superpose eq36 eq27 -- superposition 27,36, 36 into 27, unify on (0).2 in 36 and (0).2 in 27
  subsumption eq62 rfl


@[equational_result]
theorem Equation1289_implies_Equation2238 (G : Type*) [Magma G] (h : Equation1289 G) : Equation2238 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq15 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq18 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1 in 8
  have eq20 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1.1 in 8
  have eq22 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq18 eq15 -- backward demodulation 15,18
  have eq24 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq18 eq20 -- forward demodulation 20,18
  have eq26 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose eq24 eq22 -- backward demodulation 22,24
  have eq27 : sK0 ≠ sK0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).2 in 9
  subsumption eq27 rfl


@[equational_result]
theorem Equation1289_implies_Equation2441 (G : Type*) [Magma G] (h : Equation1289 G) : Equation2441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq15 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq18 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1 in 8
  have eq20 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1.1 in 8
  have eq22 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq18 eq15 -- backward demodulation 15,18
  have eq23 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := superpose eq18 eq9 -- backward demodulation 9,18
  have eq25 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq18 eq20 -- forward demodulation 20,18
  have eq27 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose eq25 eq22 -- backward demodulation 22,25
  have eq30 : sK0 ≠ sK0 := superpose eq27 eq23 -- superposition 23,27, 27 into 23, unify on (0).2 in 27 and (0).2 in 23
  subsumption eq30 rfl


@[equational_result]
theorem Equation1289_implies_Equation2847 (G : Type*) [Magma G] (h : Equation1289 G) : Equation2847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq15 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq18 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1 in 8
  have eq20 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1.1 in 8
  have eq22 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq18 eq15 -- backward demodulation 15,18
  have eq24 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq18 eq20 -- forward demodulation 20,18
  have eq26 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose eq24 eq22 -- backward demodulation 22,24
  have eq27 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := superpose eq24 eq9 -- backward demodulation 9,24
  subsumption eq27 eq26


@[equational_result]
theorem Equation1289_implies_Equation3050 (G : Type*) [Magma G] (h : Equation1289 G) : Equation3050 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq15 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq21 : sK0 ≠ sK0 := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).2 in 9
  subsumption eq21 rfl


@[equational_result]
theorem Equation1289_implies_Equation411 (G : Type*) [Magma G] (h : Equation1289 G) : Equation411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq10 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq15 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq18 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1 in 8
  have eq20 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1.1 in 8
  have eq24 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq18 eq20 -- forward demodulation 20,18
  have eq42 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq18 eq8 -- superposition 8,18, 18 into 8, unify on (0).2 in 18 and (0).1.2.1 in 8
  have eq48 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq24 eq42 -- forward demodulation 42,24
  have eq79 : sK0 ≠ sK0 := superpose eq48 eq9 -- superposition 9,48, 48 into 9, unify on (0).2 in 48 and (0).2 in 9
  subsumption eq79 rfl


@[equational_result]
theorem Equation1289_implies_Equation4380 (G : Type*) [Magma G] (h : Equation1289 G) : Equation4380 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq15 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq18 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1 in 8
  have eq46 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).2 in 9
  subsumption eq46 rfl


@[equational_result]
theorem Equation1289_implies_Equation614 (G : Type*) [Magma G] (h : Equation1289 G) : Equation614 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq15 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq18 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1 in 8
  have eq20 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1.1 in 8
  have eq23 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq18 eq9 -- backward demodulation 9,18
  have eq25 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq18 eq20 -- forward demodulation 20,18
  have eq32 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq18 eq8 -- superposition 8,18, 18 into 8, unify on (0).2 in 18 and (0).1.2.1 in 8
  have eq36 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq25 eq32 -- forward demodulation 32,25
  have eq59 : sK0 ≠ sK0 := superpose eq36 eq23 -- superposition 23,36, 36 into 23, unify on (0).2 in 36 and (0).2 in 23
  subsumption eq59 rfl


@[equational_result]
theorem Equation1290_implies_Equation961 (G : Type*) [Magma G] (h : Equation1290 G) : Equation961 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X1 X3 : G) : X1 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq19 (X0 : G) : sK0 ≠ (sK1 ◇ X0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq19 eq13


@[equational_result]
theorem Equation1291_implies_Equation1217 (G : Type*) [Magma G] (h : Equation1291 G) : Equation1217 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK3 ◇ sK4)) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : sK0 ≠ (sK1 ◇ (sK4 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation1291_implies_Equation1318 (G : Type*) [Magma G] (h : Equation1291 G) : Equation1318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


