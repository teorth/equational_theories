import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation1167_implies_Equation1647 (G : Type*) [Magma G] (h : Equation1167 G) : Equation1647 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq20 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation1167_implies_Equation4023 (G : Type*) [Magma G] (h : Equation1167 G) : Equation4023 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq20 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq22 rfl


@[equational_result]
theorem Equation1167_implies_Equation3306 (G : Type*) [Magma G] (h : Equation1167 G) : Equation3306 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq20 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq22 rfl


@[equational_result]
theorem Equation1167_implies_Equation3915 (G : Type*) [Magma G] (h : Equation1167 G) : Equation3915 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq20 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq22 rfl


@[equational_result]
theorem Equation1167_implies_Equation1780 (G : Type*) [Magma G] (h : Equation1167 G) : Equation1780 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq20 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation1167_implies_Equation3253 (G : Type*) [Magma G] (h : Equation1167 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq14 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2 in 10
  have eq17 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq11 eq14 -- forward demodulation 14,11
  have eq19 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq17 eq8 -- backward demodulation 8,17
  have eq21 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq19 eq9 -- backward demodulation 9,19
  subsumption eq21 rfl


@[equational_result]
theorem Equation1167_implies_Equation411 (G : Type*) [Magma G] (h : Equation1167 G) : Equation411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq14 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2 in 10
  have eq17 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq11 eq14 -- forward demodulation 14,11
  have eq19 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq17 eq8 -- backward demodulation 8,17
  have eq21 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq19 eq9 -- backward demodulation 9,19
  subsumption eq21 eq19


@[equational_result]
theorem Equation1167_implies_Equation1731 (G : Type*) [Magma G] (h : Equation1167 G) : Equation1731 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq20 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation1167_implies_Equation1860 (G : Type*) [Magma G] (h : Equation1167 G) : Equation1860 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK0)) := mod_symm nh
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
theorem Equation2000_implies_Equation1167 (G : Type*) [Magma G] (h : Equation2000 G) : Equation1167 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq19 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq19 eq12


@[equational_result]
theorem Equation2000_implies_Equation1085 (G : Type*) [Magma G] (h : Equation2000 G) : Equation1085 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq19 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq19 eq12


@[equational_result]
theorem Equation2000_implies_Equation1035 (G : Type*) [Magma G] (h : Equation2000 G) : Equation1035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq19 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq19 eq12


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
theorem Equation1133_implies_Equation4023 (G : Type*) [Magma G] (h : Equation1133 G) : Equation4023 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 rfl


@[equational_result]
theorem Equation1133_implies_Equation1691 (G : Type*) [Magma G] (h : Equation1133 G) : Equation1691 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1133_implies_Equation3261 (G : Type*) [Magma G] (h : Equation1133 G) : Equation3261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 rfl


@[equational_result]
theorem Equation1133_implies_Equation1647 (G : Type*) [Magma G] (h : Equation1133 G) : Equation1647 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1133_implies_Equation1731 (G : Type*) [Magma G] (h : Equation1133 G) : Equation1731 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1133_implies_Equation3334 (G : Type*) [Magma G] (h : Equation1133 G) : Equation3334 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 rfl


@[equational_result]
theorem Equation1133_implies_Equation1184 (G : Type*) [Magma G] (h : Equation1133 G) : Equation1184 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


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
theorem Equation1133_implies_Equation3306 (G : Type*) [Magma G] (h : Equation1133 G) : Equation3306 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 rfl


@[equational_result]
theorem Equation1133_implies_Equation3414 (G : Type*) [Magma G] (h : Equation1133 G) : Equation3414 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1133_implies_Equation436 (G : Type*) [Magma G] (h : Equation1133 G) : Equation436 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation1133_implies_Equation466 (G : Type*) [Magma G] (h : Equation1133 G) : Equation466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation1133_implies_Equation3278 (G : Type*) [Magma G] (h : Equation1133 G) : Equation3278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1133_implies_Equation3962 (G : Type*) [Magma G] (h : Equation1133 G) : Equation3962 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 rfl


@[equational_result]
theorem Equation1133_implies_Equation3887 (G : Type*) [Magma G] (h : Equation1133 G) : Equation3887 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 rfl


@[equational_result]
theorem Equation1133_implies_Equation1897 (G : Type*) [Magma G] (h : Equation1133 G) : Equation1897 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq34 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq34 eq12


@[equational_result]
theorem Equation1133_implies_Equation1847 (G : Type*) [Magma G] (h : Equation1133 G) : Equation1847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq34 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq34 eq12


@[equational_result]
theorem Equation1979_implies_Equation1133 (G : Type*) [Magma G] (h : Equation1979 G) : Equation1133 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X2) ◇ ((X0 ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq28 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq34 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq28 eq14 -- backward demodulation 14,28
  have eq38 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq28 eq10 -- backward demodulation 10,28
  subsumption eq38 eq34


@[equational_result]
theorem Equation1979_implies_Equation3915 (G : Type*) [Magma G] (h : Equation1979 G) : Equation3915 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X2) ◇ ((X0 ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq28 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq34 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq28 eq14 -- backward demodulation 14,28
  have eq38 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq34 eq10 -- backward demodulation 10,34
  subsumption eq38 rfl


@[equational_result]
theorem Equation1979_implies_Equation575 (G : Type*) [Magma G] (h : Equation1979 G) : Equation575 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X2) ◇ ((X0 ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq28 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq34 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq28 eq14 -- backward demodulation 14,28
  have eq38 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq34 eq10 -- backward demodulation 10,34
  subsumption eq38 eq34


@[equational_result]
theorem Equation1979_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1979 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X2) ◇ ((X0 ◇ X2) ◇ X3)) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = X1 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq27 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1.2 in 11
  have eq33 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq27 eq13 -- backward demodulation 13,27
  have eq39 : sK0 ≠ sK0 := superpose eq33 eq9 -- superposition 9,33, 33 into 9, unify on (0).2 in 33 and (0).2 in 9
  subsumption eq39 rfl


@[equational_result]
theorem Equation1979_implies_Equation3925 (G : Type*) [Magma G] (h : Equation1979 G) : Equation3925 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq28 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq92 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq28 eq10 -- superposition 10,28, 28 into 10, unify on (0).2 in 28 and (0).2 in 10
  subsumption eq92 rfl


@[equational_result]
theorem Equation1979_implies_Equation3253 (G : Type*) [Magma G] (h : Equation1979 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X2) ◇ ((X0 ◇ X2) ◇ X3)) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = X1 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq27 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1.2 in 11
  have eq33 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq27 eq13 -- backward demodulation 13,27
  have eq37 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq33 eq9 -- backward demodulation 9,33
  subsumption eq37 rfl


@[equational_result]
theorem Equation1763_implies_Equation8 (G : Type*) [Magma G] (h : Equation1763 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3)) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq18 (X1 X2 X3 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3) = (X2 ◇ X3) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2.1 in 12
  have eq29 (X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = X3 := superpose eq18 eq10 -- backward demodulation 10,18
  have eq33 : sK0 ≠ sK0 := superpose eq29 eq9 -- superposition 9,29, 29 into 9, unify on (0).2 in 29 and (0).2 in 9
  subsumption eq33 rfl


@[equational_result]
theorem Equation1763_implies_Equation1634 (G : Type*) [Magma G] (h : Equation1763 G) : Equation1634 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq9


@[equational_result]
theorem Equation1763_implies_Equation1122 (G : Type*) [Magma G] (h : Equation1763 G) : Equation1122 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 (X1 X2 X3 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3) = (X2 ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq32 (X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = X3 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq36 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq32 eq13 -- superposition 13,32, 32 into 13, unify on (0).2 in 32 and (0).2.1 in 13
  have eq40 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq36 eq14 -- backward demodulation 14,36
  subsumption eq40 eq32


@[equational_result]
theorem Equation1763_implies_Equation1202 (G : Type*) [Magma G] (h : Equation1763 G) : Equation1202 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK3 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK3 ◇ sK1)) ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 (X1 X2 X3 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3) = (X2 ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq32 (X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = X3 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq36 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq32 eq13 -- superposition 13,32, 32 into 13, unify on (0).2 in 32 and (0).2.1 in 13
  have eq40 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq36 eq14 -- backward demodulation 14,36
  subsumption eq40 eq32


@[equational_result]
theorem Equation1763_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1763 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3)) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq18 (X1 X2 X3 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3) = (X2 ◇ X3) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2.1 in 12
  have eq29 (X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = X3 := superpose eq18 eq10 -- backward demodulation 10,18
  have eq30 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq29 eq9 -- backward demodulation 9,29
  subsumption eq30 eq29


@[equational_result]
theorem Equation2024_implies_Equation4006 (G : Type*) [Magma G] (h : Equation2024 G) : Equation4006 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X3 X4 : G) : (X3 ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X0 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq42 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq42 rfl


@[equational_result]
theorem Equation2024_implies_Equation1202 (G : Type*) [Magma G] (h : Equation2024 G) : Equation1202 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK3 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq12 (X3 X4 : G) : (X3 ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X0 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq18 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq18 eq12


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
theorem Equation1912_implies_Equation1979 (G : Type*) [Magma G] (h : Equation1912 G) : Equation1979 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X0) := superpose eq12 eq14 -- superposition 14,12, 12 into 14, unify on (0).2 in 12 and (0).2.1.2 in 14
  have eq155 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X0) = ((X3 ◇ X1) ◇ X0) := superpose eq36 eq36 -- superposition 36,36, 36 into 36, unify on (0).2 in 36 and (0).1 in 36
  have eq372 (X0 : G) : sK0 ≠ ((X0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK0)) := superpose eq155 eq10 -- superposition 10,155, 155 into 10, unify on (0).2 in 155 and (0).2 in 10
  have eq1048 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq9 eq372 -- superposition 372,9, 9 into 372, unify on (0).2 in 9 and (0).2.1 in 372
  subsumption eq1048 eq12


@[equational_result]
theorem Equation1912_implies_Equation1816 (G : Type*) [Magma G] (h : Equation1912 G) : Equation1816 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK3 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq17 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X0) := superpose eq12 eq14 -- superposition 14,12, 12 into 14, unify on (0).2 in 12 and (0).2.1.2 in 14
  have eq49 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ sK0)) := superpose eq36 eq10 -- backward demodulation 10,36
  subsumption eq49 eq17


@[equational_result]
theorem Equation1912_implies_Equation1701 (G : Type*) [Magma G] (h : Equation1912 G) : Equation1701 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq17 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X0) := superpose eq12 eq14 -- superposition 14,12, 12 into 14, unify on (0).2 in 12 and (0).2.1.2 in 14
  have eq49 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := superpose eq36 eq10 -- backward demodulation 10,36
  subsumption eq49 eq17


@[equational_result]
theorem Equation1912_implies_Equation1721 (G : Type*) [Magma G] (h : Equation1912 G) : Equation1721 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq98 : sK0 ≠ sK0 := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq98 rfl


@[equational_result]
theorem Equation1912_implies_Equation1055 (G : Type*) [Magma G] (h : Equation1912 G) : Equation1055 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X0) := superpose eq12 eq14 -- superposition 14,12, 12 into 14, unify on (0).2 in 12 and (0).2.1.2 in 14
  have eq49 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0)) := superpose eq36 eq10 -- backward demodulation 10,36
  have eq131 (X1 X2 X3 : G) : (X1 ◇ X3) = ((X3 ◇ (X2 ◇ X1)) ◇ X3) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).2.1 in 36
  have eq185 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq131 eq49 -- backward demodulation 49,131
  subsumption eq185 eq12


@[equational_result]
theorem Equation1912_implies_Equation1763 (G : Type*) [Magma G] (h : Equation1912 G) : Equation1763 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq98 : sK0 ≠ sK0 := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq98 rfl


@[equational_result]
theorem Equation1202_implies_Equation1681 (G : Type*) [Magma G] (h : Equation1202 G) : Equation1681 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ ((X4 ◇ X3) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X3 X4 : G) : (X3 ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq18 (X0 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ ((X4 ◇ X3) ◇ X5)) = X5 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq26 : sK0 ≠ sK0 := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation1202_implies_Equation3972 (G : Type*) [Magma G] (h : Equation1202 G) : Equation3972 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X3 X4 : G) : (X3 ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq35 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq35 rfl


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
theorem Equation1202_implies_Equation1657 (G : Type*) [Magma G] (h : Equation1202 G) : Equation1657 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ ((X4 ◇ X3) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X3 X4 : G) : (X3 ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq18 (X0 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ ((X4 ◇ X3) ◇ X5)) = X5 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq26 : sK0 ≠ sK0 := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation1202_implies_Equation1668 (G : Type*) [Magma G] (h : Equation1202 G) : Equation1668 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ ((X4 ◇ X3) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X3 X4 : G) : (X3 ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq18 (X0 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ ((X4 ◇ X3) ◇ X5)) = X5 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq26 : sK0 ≠ sK0 := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation1816_implies_Equation3897 (G : Type*) [Magma G] (h : Equation1816 G) : Equation3897 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X1 X2 X3 X4 : G) : ((X2 ◇ X1) ◇ X3) = ((X4 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X2 X3 X4 X5 : G) : (X3 ◇ X4) = ((X5 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ (sK2 ◇ sK0)) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq36 (X3 X5 : G) : (X3 ◇ (X3 ◇ X5)) = X5 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq52 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq36 eq26 -- superposition 26,36, 36 into 26, unify on (0).2 in 36 and (0).2.1 in 26
  subsumption eq52 rfl


@[equational_result]
theorem Equation1816_implies_Equation4606 (G : Type*) [Magma G] (h : Equation1816 G) : Equation4606 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X1 X2 X3 X4 : G) : ((X2 ◇ X1) ◇ X3) = ((X4 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq26 eq13


@[equational_result]
theorem Equation1816_implies_Equation4040 (G : Type*) [Magma G] (h : Equation1816 G) : Equation4040 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X1 X2 X3 X4 : G) : ((X2 ◇ X1) ◇ X3) = ((X4 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X2 X3 X4 X5 : G) : (X3 ◇ X4) = ((X5 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq26 (X0 : G) : (sK0 ◇ sK1) ≠ ((X0 ◇ (sK3 ◇ sK0)) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq36 (X3 X5 : G) : (X3 ◇ (X3 ◇ X5)) = X5 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq52 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq36 eq26 -- superposition 26,36, 36 into 26, unify on (0).2 in 36 and (0).2.1 in 26
  subsumption eq52 rfl


@[equational_result]
theorem Equation1816_implies_Equation1167 (G : Type*) [Magma G] (h : Equation1816 G) : Equation1167 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X1 X2 X3 X4 : G) : ((X2 ◇ X1) ◇ X3) = ((X4 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X2 X3 X4 X5 : G) : (X3 ◇ X4) = ((X5 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq26 (X0 : G) : sK0 ≠ (sK1 ◇ ((X0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  have eq36 (X3 X5 : G) : (X3 ◇ (X3 ◇ X5)) = X5 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq42 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X3) = (X1 ◇ X3) := superpose eq36 eq13 -- superposition 13,36, 36 into 13, unify on (0).2 in 36 and (0).2.1 in 13
  have eq49 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq42 eq26 -- backward demodulation 26,42
  subsumption eq49 eq36


@[equational_result]
theorem Equation1816_implies_Equation1112 (G : Type*) [Magma G] (h : Equation1816 G) : Equation1112 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X1 X2 X3 X4 : G) : ((X2 ◇ X1) ◇ X3) = ((X4 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X2 X3 X4 X5 : G) : (X3 ◇ X4) = ((X5 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq26 (X0 : G) : sK0 ≠ (sK1 ◇ ((X0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  have eq36 (X3 X5 : G) : (X3 ◇ (X3 ◇ X5)) = X5 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq42 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X3) = (X1 ◇ X3) := superpose eq36 eq13 -- superposition 13,36, 36 into 13, unify on (0).2 in 36 and (0).2.1 in 13
  have eq49 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq42 eq26 -- backward demodulation 26,42
  subsumption eq49 eq36


@[equational_result]
theorem Equation1816_implies_Equation4689 (G : Type*) [Magma G] (h : Equation1816 G) : Equation4689 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK3 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq13 (X1 X2 X3 X4 : G) : ((X2 ◇ X1) ◇ X3) = ((X4 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ ((X0 ◇ sK1) ◇ sK2) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq26 eq13


@[equational_result]
theorem Equation1816_implies_Equation1958 (G : Type*) [Magma G] (h : Equation1816 G) : Equation1958 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X1 X2 X3 X4 : G) : ((X2 ◇ X1) ◇ X3) = ((X4 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X2 X3 X4 X5 : G) : (X3 ◇ X4) = ((X5 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq26 (X0 : G) : sK0 ≠ ((X0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq36 (X3 X5 : G) : (X3 ◇ (X3 ◇ X5)) = X5 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq52 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq36 eq26 -- superposition 26,36, 36 into 26, unify on (0).2 in 36 and (0).2.1 in 26
  subsumption eq52 eq36


@[equational_result]
theorem Equation1816_implies_Equation3867 (G : Type*) [Magma G] (h : Equation1816 G) : Equation3867 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X1 X2 X3 X4 : G) : ((X2 ◇ X1) ◇ X3) = ((X4 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X2 X3 X4 X5 : G) : (X3 ◇ X4) = ((X5 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq36 (X3 X5 : G) : (X3 ◇ (X3 ◇ X5)) = X5 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq52 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq36 eq26 -- superposition 26,36, 36 into 26, unify on (0).2 in 36 and (0).2.1 in 26
  subsumption eq52 rfl


@[equational_result]
theorem Equation1816_implies_Equation1096 (G : Type*) [Magma G] (h : Equation1816 G) : Equation1096 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X1 X2 X3 X4 : G) : ((X2 ◇ X1) ◇ X3) = ((X4 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X2 X3 X4 X5 : G) : (X3 ◇ X4) = ((X5 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq26 (X0 : G) : sK0 ≠ (sK1 ◇ ((X0 ◇ (sK2 ◇ sK1)) ◇ sK0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  have eq36 (X3 X5 : G) : (X3 ◇ (X3 ◇ X5)) = X5 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq42 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X3) = (X1 ◇ X3) := superpose eq36 eq13 -- superposition 13,36, 36 into 13, unify on (0).2 in 36 and (0).2.1 in 13
  have eq49 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq42 eq26 -- backward demodulation 26,42
  subsumption eq49 eq36


@[equational_result]
theorem Equation1816_implies_Equation2024 (G : Type*) [Magma G] (h : Equation1816 G) : Equation2024 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK3 ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X1 X2 X3 X4 : G) : ((X2 ◇ X1) ◇ X3) = ((X4 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X2 X3 X4 X5 : G) : (X3 ◇ X4) = ((X5 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq26 (X0 : G) : sK0 ≠ ((X0 ◇ (sK2 ◇ sK3)) ◇ (sK3 ◇ sK0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq36 (X3 X5 : G) : (X3 ◇ (X3 ◇ X5)) = X5 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq52 : sK0 ≠ (sK3 ◇ (sK3 ◇ sK0)) := superpose eq36 eq26 -- superposition 26,36, 36 into 26, unify on (0).2 in 36 and (0).2.1 in 26
  subsumption eq52 eq36


@[equational_result]
theorem Equation1816_implies_Equation1025 (G : Type*) [Magma G] (h : Equation1816 G) : Equation1025 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X1 X2 X3 X4 : G) : ((X2 ◇ X1) ◇ X3) = ((X4 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X2 X3 X4 X5 : G) : (X3 ◇ X4) = ((X5 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq26 (X0 : G) : sK0 ≠ (sK0 ◇ ((X0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  have eq36 (X3 X5 : G) : (X3 ◇ (X3 ◇ X5)) = X5 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq42 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X3) = (X1 ◇ X3) := superpose eq36 eq13 -- superposition 13,36, 36 into 13, unify on (0).2 in 36 and (0).2.1 in 13
  have eq49 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq42 eq26 -- backward demodulation 26,42
  subsumption eq49 eq36


@[equational_result]
theorem Equation2169_implies_Equation1705 (G : Type*) [Magma G] (h : Equation2169 G) : Equation1705 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation2169_implies_Equation3955 (G : Type*) [Magma G] (h : Equation2169 G) : Equation3955 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq18 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq38 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq38 rfl


@[equational_result]
theorem Equation2169_implies_Equation1691 (G : Type*) [Magma G] (h : Equation2169 G) : Equation1691 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq77 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq77 rfl


@[equational_result]
theorem Equation2169_implies_Equation1629 (G : Type*) [Magma G] (h : Equation2169 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq19 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq19 rfl


@[equational_result]
theorem Equation2169_implies_Equation2090 (G : Type*) [Magma G] (h : Equation2169 G) : Equation2090 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq18 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq32 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X2)) = X2 := superpose eq9 eq18 -- superposition 18,9, 9 into 18, unify on (0).2 in 9 and (0).1 in 18
  have eq138 : sK0 ≠ sK0 := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2 in 10
  subsumption eq138 rfl


@[equational_result]
theorem Equation1705_implies_Equation2169 (G : Type*) [Magma G] (h : Equation1705 G) : Equation2169 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X0) ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X1 X3 X4 : G) : (((X1 ◇ X3) ◇ X4) ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1.1 in 12
  have eq50 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1705_implies_Equation3353 (G : Type*) [Magma G] (h : Equation1705 G) : Equation3353 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X0) ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 (X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq113 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq113 rfl


@[equational_result]
theorem Equation1705_implies_Equation3862 (G : Type*) [Magma G] (h : Equation1705 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X2 ◇ X0) ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq21 (X2 X3 : G) : (X2 ◇ X3) = ((X3 ◇ (X2 ◇ X3)) ◇ X3) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.2 in 8
  have eq125 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq21 eq9 -- superposition 9,21, 21 into 9, unify on (0).2 in 21 and (0).2 in 9
  subsumption eq125 rfl


@[equational_result]
theorem Equation1705_implies_Equation2035 (G : Type*) [Magma G] (h : Equation1705 G) : Equation2035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X2 ◇ X0) ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq13 (X1 X3 X4 : G) : (((X1 ◇ X3) ◇ X4) ◇ (X3 ◇ X4)) = X4 := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1.1.1.1 in 11
  have eq49 : sK0 ≠ sK0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2 in 9
  subsumption eq49 rfl


@[equational_result]
theorem Equation1705_implies_Equation2127 (G : Type*) [Magma G] (h : Equation1705 G) : Equation2127 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X0) ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X1 X3 X4 : G) : (((X1 ◇ X3) ◇ X4) ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1.1 in 12
  have eq50 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1705_implies_Equation2087 (G : Type*) [Magma G] (h : Equation1705 G) : Equation2087 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X0) ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X1 X3 X4 : G) : (((X1 ◇ X3) ◇ X4) ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1.1 in 12
  have eq50 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1705_implies_Equation2053 (G : Type*) [Magma G] (h : Equation1705 G) : Equation2053 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X0) ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X1 X3 X4 : G) : (((X1 ◇ X3) ◇ X4) ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1.1 in 12
  have eq50 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1697_implies_Equation2165 (G : Type*) [Magma G] (h : Equation1697 G) : Equation2165 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq45 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2 in 15
  have eq50 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.1 in 13
  have eq164 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq45 eq9 -- superposition 9,45, 45 into 9, unify on (0).2 in 45 and (0).1.2 in 9
  have eq224 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq164 eq164 -- superposition 164,164, 164 into 164, unify on (0).2 in 164 and (0).1.1 in 164
  have eq323 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq50 eq15 -- superposition 15,50, 50 into 15, unify on (0).2 in 50 and (0).1.2 in 15
  have eq929 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq224 eq13 -- superposition 13,224, 224 into 13, unify on (0).2 in 224 and (0).2.1 in 13
  have eq963 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq323 eq929 -- forward demodulation 929,323
  have eq1132 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X2)) = X2 := superpose eq963 eq9 -- superposition 9,963, 963 into 9, unify on (0).2 in 963 and (0).1.2.1 in 9
  have eq2222 : sK0 ≠ sK0 := superpose eq1132 eq10 -- superposition 10,1132, 1132 into 10, unify on (0).2 in 1132 and (0).2 in 10
  subsumption eq2222 rfl


@[equational_result]
theorem Equation1697_implies_Equation2169 (G : Type*) [Magma G] (h : Equation1697 G) : Equation2169 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation1697_implies_Equation4065 (G : Type*) [Magma G] (h : Equation1697 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq14 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq46 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).2.1 in 12
  have eq343 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq46 eq9 -- superposition 9,46, 46 into 9, unify on (0).2 in 46 and (0).2 in 9
  subsumption eq343 rfl


@[equational_result]
theorem Equation1697_implies_Equation1837 (G : Type*) [Magma G] (h : Equation1697 G) : Equation1837 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq45 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2 in 15
  have eq50 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.1 in 13
  have eq164 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq45 eq9 -- superposition 9,45, 45 into 9, unify on (0).2 in 45 and (0).1.2 in 9
  have eq224 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq164 eq164 -- superposition 164,164, 164 into 164, unify on (0).2 in 164 and (0).1.1 in 164
  have eq323 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq50 eq15 -- superposition 15,50, 50 into 15, unify on (0).2 in 50 and (0).1.2 in 15
  have eq929 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq224 eq13 -- superposition 13,224, 224 into 13, unify on (0).2 in 224 and (0).2.1 in 13
  have eq963 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq323 eq929 -- forward demodulation 929,323
  have eq1108 : sK0 ≠ sK0 := superpose eq963 eq10 -- superposition 10,963, 963 into 10, unify on (0).2 in 963 and (0).2 in 10
  subsumption eq1108 rfl


@[equational_result]
theorem Equation1697_implies_Equation1867 (G : Type*) [Magma G] (h : Equation1697 G) : Equation1867 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq45 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2 in 15
  have eq50 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.1 in 13
  have eq164 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq45 eq9 -- superposition 9,45, 45 into 9, unify on (0).2 in 45 and (0).1.2 in 9
  have eq224 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq164 eq164 -- superposition 164,164, 164 into 164, unify on (0).2 in 164 and (0).1.1 in 164
  have eq323 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq50 eq15 -- superposition 15,50, 50 into 15, unify on (0).2 in 50 and (0).1.2 in 15
  have eq913 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq224 eq13 -- superposition 13,224, 224 into 13, unify on (0).2 in 224 and (0).2.1 in 13
  have eq961 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq323 eq913 -- forward demodulation 913,323
  have eq1108 : sK0 ≠ sK0 := superpose eq961 eq10 -- superposition 10,961, 961 into 10, unify on (0).2 in 961 and (0).2 in 10
  subsumption eq1108 rfl


@[equational_result]
theorem Equation1697_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1697 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq14 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq44 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq11 eq14 -- superposition 14,11, 11 into 14, unify on (0).2 in 11 and (0).1.2 in 14
  have eq49 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).2.1 in 12
  have eq163 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq44 eq8 -- superposition 8,44, 44 into 8, unify on (0).2 in 44 and (0).1.2 in 8
  have eq223 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq163 eq163 -- superposition 163,163, 163 into 163, unify on (0).2 in 163 and (0).1.1 in 163
  have eq322 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq49 eq14 -- superposition 14,49, 49 into 14, unify on (0).2 in 49 and (0).1.2 in 14
  have eq928 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq223 eq12 -- superposition 12,223, 223 into 12, unify on (0).2 in 223 and (0).2.1 in 12
  have eq962 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq322 eq928 -- forward demodulation 928,322
  have eq1107 : sK0 ≠ sK0 := superpose eq962 eq9 -- superposition 9,962, 962 into 9, unify on (0).2 in 962 and (0).2 in 9
  subsumption eq1107 rfl


@[equational_result]
theorem Equation1697_implies_Equation1847 (G : Type*) [Magma G] (h : Equation1697 G) : Equation1847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq45 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2 in 15
  have eq50 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.1 in 13
  have eq164 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq45 eq9 -- superposition 9,45, 45 into 9, unify on (0).2 in 45 and (0).1.2 in 9
  have eq224 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq164 eq164 -- superposition 164,164, 164 into 164, unify on (0).2 in 164 and (0).1.1 in 164
  have eq323 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq50 eq15 -- superposition 15,50, 50 into 15, unify on (0).2 in 50 and (0).1.2 in 15
  have eq913 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq224 eq13 -- superposition 13,224, 224 into 13, unify on (0).2 in 224 and (0).2.1 in 13
  have eq961 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq323 eq913 -- forward demodulation 913,323
  have eq1108 : sK0 ≠ sK0 := superpose eq961 eq10 -- superposition 10,961, 961 into 10, unify on (0).2 in 961 and (0).2 in 10
  subsumption eq1108 rfl


@[equational_result]
theorem Equation1697_implies_Equation4083 (G : Type*) [Magma G] (h : Equation1697 G) : Equation4083 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq50 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.1 in 13
  have eq327 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq50 eq10 -- superposition 10,50, 50 into 10, unify on (0).2 in 50 and (0).2 in 10
  subsumption eq327 rfl


@[equational_result]
theorem Equation1697_implies_Equation3887 (G : Type*) [Magma G] (h : Equation1697 G) : Equation3887 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X1) = (X1 ◇ (((X0 ◇ X1) ◇ X3) ◇ ((X0 ◇ X2) ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq76 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).2.2 in 11
  have eq598 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq76 eq10 -- superposition 10,76, 76 into 10, unify on (0).2 in 76 and (0).2 in 10
  subsumption eq598 rfl


@[equational_result]
theorem Equation1697_implies_Equation3877 (G : Type*) [Magma G] (h : Equation1697 G) : Equation3877 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq45 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2 in 15
  have eq50 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.1 in 13
  have eq164 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq45 eq9 -- superposition 9,45, 45 into 9, unify on (0).2 in 45 and (0).1.2 in 9
  have eq323 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq50 eq15 -- superposition 15,50, 50 into 15, unify on (0).2 in 50 and (0).1.2 in 15
  have eq438 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq164 eq323 -- superposition 323,164, 164 into 323, unify on (0).2 in 164 and (0).1.2 in 323
  have eq1593 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq438 eq10 -- superposition 10,438, 438 into 10, unify on (0).2 in 438 and (0).2 in 10
  subsumption eq1593 rfl


@[equational_result]
theorem Equation1697_implies_Equation2124 (G : Type*) [Magma G] (h : Equation1697 G) : Equation2124 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq50 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.1 in 13
  have eq323 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq50 eq15 -- superposition 15,50, 50 into 15, unify on (0).2 in 50 and (0).1.2 in 15
  have eq441 : sK0 ≠ sK0 := superpose eq323 eq10 -- superposition 10,323, 323 into 10, unify on (0).2 in 323 and (0).2 in 10
  subsumption eq441 rfl


@[equational_result]
theorem Equation1697_implies_Equation1637 (G : Type*) [Magma G] (h : Equation1697 G) : Equation1637 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq45 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2 in 15
  have eq164 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq45 eq9 -- superposition 9,45, 45 into 9, unify on (0).2 in 45 and (0).1.2 in 9
  have eq235 : sK0 ≠ sK0 := superpose eq164 eq10 -- superposition 10,164, 164 into 10, unify on (0).2 in 164 and (0).2 in 10
  subsumption eq235 rfl


@[equational_result]
theorem Equation1697_implies_Equation2161 (G : Type*) [Magma G] (h : Equation1697 G) : Equation2161 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq50 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.1 in 13
  have eq323 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq50 eq15 -- superposition 15,50, 50 into 15, unify on (0).2 in 50 and (0).1.2 in 15
  have eq441 : sK0 ≠ sK0 := superpose eq323 eq10 -- superposition 10,323, 323 into 10, unify on (0).2 in 323 and (0).2 in 10
  subsumption eq441 rfl


@[equational_result]
theorem Equation1697_implies_Equation1640 (G : Type*) [Magma G] (h : Equation1697 G) : Equation1640 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq45 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2 in 15
  have eq164 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq45 eq9 -- superposition 9,45, 45 into 9, unify on (0).2 in 45 and (0).1.2 in 9
  have eq235 : sK0 ≠ sK0 := superpose eq164 eq10 -- superposition 10,164, 164 into 10, unify on (0).2 in 164 and (0).2 in 10
  subsumption eq235 rfl


@[equational_result]
theorem Equation1697_implies_Equation151 (G : Type*) [Magma G] (h : Equation1697 G) : Equation151 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq14 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq44 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq11 eq14 -- superposition 14,11, 11 into 14, unify on (0).2 in 11 and (0).1.2 in 14
  have eq163 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq44 eq8 -- superposition 8,44, 44 into 8, unify on (0).2 in 44 and (0).1.2 in 8
  have eq234 : sK0 ≠ sK0 := superpose eq163 eq9 -- superposition 9,163, 163 into 9, unify on (0).2 in 163 and (0).2 in 9
  subsumption eq234 rfl


@[equational_result]
theorem Equation1697_implies_Equation4067 (G : Type*) [Magma G] (h : Equation1697 G) : Equation4067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq45 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2 in 15
  have eq164 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq45 eq9 -- superposition 9,45, 45 into 9, unify on (0).2 in 45 and (0).1.2 in 9
  have eq243 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq164 eq13 -- superposition 13,164, 164 into 13, unify on (0).2 in 164 and (0).2.1 in 13
  have eq1330 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq243 eq10 -- superposition 10,243, 243 into 10, unify on (0).2 in 243 and (0).2 in 10
  subsumption eq1330 rfl


@[equational_result]
theorem Equation1697_implies_Equation2050 (G : Type*) [Magma G] (h : Equation1697 G) : Equation2050 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq50 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.1 in 13
  have eq323 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq50 eq15 -- superposition 15,50, 50 into 15, unify on (0).2 in 50 and (0).1.2 in 15
  have eq441 : sK0 ≠ sK0 := superpose eq323 eq10 -- superposition 10,323, 323 into 10, unify on (0).2 in 323 and (0).2 in 10
  subsumption eq441 rfl


@[equational_result]
theorem Equation1697_implies_Equation1857 (G : Type*) [Magma G] (h : Equation1697 G) : Equation1857 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq45 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2 in 15
  have eq50 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.1 in 13
  have eq164 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq45 eq9 -- superposition 9,45, 45 into 9, unify on (0).2 in 45 and (0).1.2 in 9
  have eq224 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq164 eq164 -- superposition 164,164, 164 into 164, unify on (0).2 in 164 and (0).1.1 in 164
  have eq323 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq50 eq15 -- superposition 15,50, 50 into 15, unify on (0).2 in 50 and (0).1.2 in 15
  have eq913 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq224 eq13 -- superposition 13,224, 224 into 13, unify on (0).2 in 224 and (0).2.1 in 13
  have eq961 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq323 eq913 -- forward demodulation 913,323
  have eq1108 : sK0 ≠ sK0 := superpose eq961 eq10 -- superposition 10,961, 961 into 10, unify on (0).2 in 961 and (0).2 in 10
  subsumption eq1108 rfl


@[equational_result]
theorem Equation2165_implies_Equation1697 (G : Type*) [Magma G] (h : Equation2165 G) : Equation1697 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X0 ◇ X2)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 X2 : G) : (X0 ◇ X2) = ((X2 ◇ (X0 ◇ X2)) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq28 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2)) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq80 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.1 in 13
  have eq138 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq20 eq9 -- superposition 9,20, 20 into 9, unify on (0).2 in 20 and (0).1.1 in 9
  have eq499 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq80 -- superposition 80,12, 12 into 80, unify on (0).2 in 12 and (0).2.1 in 80
  have eq537 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq138 eq499 -- forward demodulation 499,138
  have eq570 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq537 eq28 -- superposition 28,537, 537 into 28, unify on (0).2 in 537 and (0).1.2.1 in 28
  have eq1675 : sK0 ≠ sK0 := superpose eq570 eq10 -- superposition 10,570, 570 into 10, unify on (0).2 in 570 and (0).2 in 10
  subsumption eq1675 rfl


@[equational_result]
theorem Equation2165_implies_Equation3258 (G : Type*) [Magma G] (h : Equation2165 G) : Equation3258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq20 (X0 X2 : G) : (X0 ◇ X2) = ((X2 ◇ (X0 ◇ X2)) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq138 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq20 eq9 -- superposition 9,20, 20 into 9, unify on (0).2 in 20 and (0).1.1 in 9
  have eq166 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq138 eq9 -- superposition 9,138, 138 into 9, unify on (0).2 in 138 and (0).1.1 in 9
  have eq1200 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq166 eq10 -- superposition 10,166, 166 into 10, unify on (0).2 in 166 and (0).2 in 10
  subsumption eq1200 rfl


@[equational_result]
theorem Equation2165_implies_Equation1631 (G : Type*) [Magma G] (h : Equation2165 G) : Equation1631 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq20 (X0 X2 : G) : (X0 ◇ X2) = ((X2 ◇ (X0 ◇ X2)) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq138 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq20 eq9 -- superposition 9,20, 20 into 9, unify on (0).2 in 20 and (0).1.1 in 9
  have eq161 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq138 eq138 -- superposition 138,138, 138 into 138, unify on (0).2 in 138 and (0).1.2 in 138
  have eq433 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq161 eq9 -- superposition 9,161, 161 into 9, unify on (0).2 in 161 and (0).1.1 in 9
  have eq756 : sK0 ≠ sK0 := superpose eq433 eq10 -- superposition 10,433, 433 into 10, unify on (0).2 in 433 and (0).2 in 10
  subsumption eq756 rfl


@[equational_result]
theorem Equation1370_implies_Equation2203 (G : Type*) [Magma G] (h : Equation1370 G) : Equation2203 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK2) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X1 X2 X3 : G) : (X2 ◇ X3) = ((X2 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq20 (X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X2 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3)) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq25 (X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X3)) = X3 := superpose eq18 eq20 -- forward demodulation 20,18
  have eq57 : sK0 ≠ sK0 := superpose eq25 eq10 -- superposition 10,25, 25 into 10, unify on (0).2 in 25 and (0).2 in 10
  subsumption eq57 rfl


@[equational_result]
theorem Equation2203_implies_Equation1370 (G : Type*) [Magma G] (h : Equation2203 G) : Equation1370 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK1) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq31 (X1 X2 X3 : G) : (X2 ◇ (((X1 ◇ X2) ◇ X2) ◇ X3)) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq47 : sK0 ≠ sK0 := superpose eq31 eq10 -- superposition 10,31, 31 into 10, unify on (0).2 in 31 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation179_implies_Equation127 (G : Type*) [Magma G] (h : Equation179 G) : Equation127 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation179_implies_Equation99 (G : Type*) [Magma G] (h : Equation179 G) : Equation99 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq14 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq14 rfl


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
theorem Equation1299_implies_Equation1336 (G : Type*) [Magma G] (h : Equation1299 G) : Equation1336 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK2) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ ((X1 ◇ X3) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation1299_implies_Equation2100 (G : Type*) [Magma G] (h : Equation1299 G) : Equation2100 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ ((X1 ◇ X3) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ X2) ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X0)) = X0 := superpose eq15 eq12 -- backward demodulation 12,15
  have eq26 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation1299_implies_Equation1353 (G : Type*) [Magma G] (h : Equation1299 G) : Equation1353 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK0) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ ((X1 ◇ X3) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation1299_implies_Equation3925 (G : Type*) [Magma G] (h : Equation1299 G) : Equation3925 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ ((X1 ◇ X3) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq62 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq62 rfl


@[equational_result]
theorem Equation1299_implies_Equation2078 (G : Type*) [Magma G] (h : Equation1299 G) : Equation2078 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ ((X1 ◇ X3) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ X2) ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X0)) = X0 := superpose eq15 eq12 -- backward demodulation 12,15
  have eq26 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation1299_implies_Equation1325 (G : Type*) [Magma G] (h : Equation1299 G) : Equation1325 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ ((X1 ◇ X3) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation1299_implies_Equation2124 (G : Type*) [Magma G] (h : Equation1299 G) : Equation2124 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ ((X1 ◇ X3) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ X2) ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X0)) = X0 := superpose eq15 eq12 -- backward demodulation 12,15
  have eq26 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation1299_implies_Equation1238 (G : Type*) [Magma G] (h : Equation1299 G) : Equation1238 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ ((X1 ◇ X3) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation1336_implies_Equation1299 (G : Type*) [Magma G] (h : Equation1336 G) : Equation1299 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK2) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation1336_implies_Equation1387 (G : Type*) [Magma G] (h : Equation1336 G) : Equation1387 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK2) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation1336_implies_Equation1405 (G : Type*) [Magma G] (h : Equation1336 G) : Equation1405 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK3) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation1336_implies_Equation4666 (G : Type*) [Magma G] (h : Equation1336 G) : Equation4666 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X3)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq62 (X2 X3 X4 X5 : G) : ((X2 ◇ X3) ◇ X4) = ((X5 ◇ X3) ◇ X4) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).2.1.2 in 16
  have eq220 (X0 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ ((X0 ◇ sK1) ◇ sK1) := superpose eq62 eq10 -- superposition 10,62, 62 into 10, unify on (0).2 in 62 and (0).2 in 10
  subsumption eq220 eq62


@[equational_result]
theorem Equation1336_implies_Equation3862 (G : Type*) [Magma G] (h : Equation1336 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.2 in 10
  have eq77 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).2 in 9
  subsumption eq77 rfl


@[equational_result]
theorem Equation1336_implies_Equation3867 (G : Type*) [Magma G] (h : Equation1336 G) : Equation3867 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq78 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq78 rfl


@[equational_result]
theorem Equation1336_implies_Equation1288 (G : Type*) [Magma G] (h : Equation1336 G) : Equation1288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation1336_implies_Equation3877 (G : Type*) [Magma G] (h : Equation1336 G) : Equation3877 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq78 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq78 rfl


@[equational_result]
theorem Equation2173_implies_Equation1962 (G : Type*) [Magma G] (h : Equation2173 G) : Equation1962 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X2 X4 X5 : G) : ((X2 ◇ X4) ◇ (X5 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X2 X3 X4 : G) : (X3 ◇ X2) = (X2 ◇ (X4 ◇ (X3 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X2 X3 : G) : (X3 ◇ X2) = (X2 ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq32 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK0)) := superpose eq24 eq10 -- backward demodulation 10,24
  have eq33 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := superpose eq24 eq32 -- forward demodulation 32,24
  have eq37 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq11 eq24 -- superposition 24,11, 11 into 24, unify on (0).2 in 11 and (0).2 in 24
  have eq60 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq37 eq33 -- backward demodulation 33,37
  subsumption eq60 eq37


@[equational_result]
theorem Equation1709_implies_Equation2130 (G : Type*) [Magma G] (h : Equation1709 G) : Equation2130 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1709_implies_Equation2156 (G : Type*) [Magma G] (h : Equation1709 G) : Equation2156 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK2) ◇ (sK3 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = ((X2 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq33 : sK0 ≠ ((sK2 ◇ sK2) ◇ (sK3 ◇ sK0)) := superpose eq26 eq10 -- backward demodulation 10,26
  have eq53 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X1)) = X1 := superpose eq12 eq26 -- superposition 26,12, 12 into 26, unify on (0).2 in 12 and (0).1 in 26
  have eq55 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X2) := superpose eq9 eq26 -- superposition 26,9, 9 into 26, unify on (0).2 in 9 and (0).2.1 in 26
  have eq87 : sK0 ≠ ((sK2 ◇ sK2) ◇ (sK0 ◇ sK0)) := superpose eq55 eq33 -- backward demodulation 33,55
  subsumption eq87 eq53


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
theorem Equation1806_implies_Equation176 (G : Type*) [Magma G] (h : Equation1806 G) : Equation176 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ X5) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X3) = (X4 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq22 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X3) = (X4 ◇ X3) := superpose eq11 eq15 -- forward demodulation 15,11
  have eq65 (X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ X1) := superpose eq22 eq22 -- superposition 22,22, 22 into 22, unify on (0).2 in 22 and (0).1 in 22
  have eq77 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X1)) = X1 := superpose eq22 eq11 -- superposition 11,22, 22 into 11, unify on (0).2 in 22 and (0).1.2 in 11
  have eq157 (X0 : G) : sK0 ≠ (X0 ◇ (sK0 ◇ sK0)) := superpose eq65 eq10 -- superposition 10,65, 65 into 10, unify on (0).2 in 65 and (0).2 in 10
  subsumption eq157 eq77


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
theorem Equation2107_implies_Equation1945 (G : Type*) [Magma G] (h : Equation2107 G) : Equation1945 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq18 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq18 eq12


@[equational_result]
theorem Equation1755_implies_Equation1900 (G : Type*) [Magma G] (h : Equation1755 G) : Equation1900 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X2 X3 : G) : (X2 ◇ ((X3 ◇ X3) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq22 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X1 ◇ X0) := superpose eq11 eq15 -- forward demodulation 15,11
  have eq56 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = X0 := superpose eq22 eq11 -- superposition 11,22, 22 into 11, unify on (0).2 in 22 and (0).1.2 in 11
  have eq67 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq56 eq10 -- backward demodulation 10,56
  subsumption eq67 eq56


@[equational_result]
theorem Equation2111_implies_Equation1755 (G : Type*) [Magma G] (h : Equation2111 G) : Equation1755 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X1 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq18 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X1 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq34 (X0 : G) : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK0 ◇ X0) ◇ sK0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq34 eq18


@[equational_result]
theorem Equation1945_implies_Equation2111 (G : Type*) [Magma G] (h : Equation1945 G) : Equation2111 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK2) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq21 (X0 X2 X3 : G) : (X0 ◇ X2) = (X3 ◇ X2) := superpose eq13 eq12 -- backward demodulation 12,13
  have eq22 (X0 X2 X3 : G) : (X3 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).1 in 21
  have eq30 (X0 : G) : sK0 ≠ ((X0 ◇ sK2) ◇ (sK1 ◇ sK0)) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2.1 in 10
  subsumption eq30 eq22


@[equational_result]
theorem Equation1945_implies_Equation1067 (G : Type*) [Magma G] (h : Equation1945 G) : Equation1067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq21 (X0 X2 X3 : G) : (X0 ◇ X2) = (X3 ◇ X2) := superpose eq13 eq12 -- backward demodulation 12,13
  have eq22 (X0 X2 X3 : G) : (X3 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).1 in 21
  have eq61 : sK0 ≠ (sK0 ◇ (sK3 ◇ sK0)) := superpose eq22 eq10 -- backward demodulation 10,22
  subsumption eq61 eq22


@[equational_result]
theorem Equation2148_implies_Equation1945 (G : Type*) [Magma G] (h : Equation2148 G) : Equation1945 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X3)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq20 : sK0 ≠ (sK2 ◇ (sK1 ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq20 eq14


@[equational_result]
theorem Equation169_implies_Equation1278 (G : Type*) [Magma G] (h : Equation169 G) : Equation1278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq13 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq18 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ sK0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.2 in 12
  subsumption eq18 eq13


@[equational_result]
theorem Equation169_implies_Equation1291 (G : Type*) [Magma G] (h : Equation169 G) : Equation1291 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK1) ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq13 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq18 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ sK0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.2 in 12
  subsumption eq18 eq13


@[equational_result]
theorem Equation1344_implies_Equation1291 (G : Type*) [Magma G] (h : Equation1344 G) : Equation1291 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK1) ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation1344_implies_Equation3296 (G : Type*) [Magma G] (h : Equation1344 G) : Equation3296 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq34 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq16 eq14 -- superposition 14,16, 16 into 14, unify on (0).2 in 16 and (0).2 in 14
  subsumption eq34 eq16


@[equational_result]
theorem Equation1366_implies_Equation2178 (G : Type*) [Magma G] (h : Equation1366 G) : Equation2178 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ ((X2 ◇ X3) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X3) = (X1 ◇ (X3 ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq19 (X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq57 (X0 X1 X2 X3 : G) : ((((X2 ◇ (X3 ◇ X0)) ◇ X1) ◇ X1) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X1) ◇ X1))) = (X0 ◇ ((X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X1) ◇ X1)) ◇ ((((X2 ◇ (X3 ◇ X0)) ◇ X1) ◇ X1) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X1) ◇ X1))))) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).1.1 in 19
  have eq59 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.2 in 19
  have eq84 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq59 eq9 -- superposition 9,59, 59 into 9, unify on (0).2 in 59 and (0).1.2 in 9
  have eq97 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X3) = (X1 ◇ X3) := superpose eq84 eq12 -- backward demodulation 12,84
  have eq102 (X0 X1 X2 X3 : G) : ((((X2 ◇ (X3 ◇ X0)) ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ ((((X2 ◇ (X3 ◇ X0)) ◇ X1) ◇ X1) ◇ X1))) := superpose eq84 eq57 -- backward demodulation 57,84
  have eq130 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((((X2 ◇ (X3 ◇ X0)) ◇ X1) ◇ X1) ◇ X1) := superpose eq9 eq102 -- forward demodulation 102,9
  have eq131 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq97 eq130 -- forward demodulation 130,97
  have eq136 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq131 eq84 -- backward demodulation 84,131
  have eq138 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := superpose eq131 eq9 -- backward demodulation 9,131
  have eq182 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq136 eq138 -- superposition 138,136, 136 into 138, unify on (0).2 in 136 and (0).1.2 in 138
  have eq183 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq136 eq182 -- forward demodulation 182,136
  have eq205 : sK0 ≠ sK0 := superpose eq183 eq10 -- superposition 10,183, 183 into 10, unify on (0).2 in 183 and (0).2 in 10
  subsumption eq205 rfl


@[equational_result]
theorem Equation2217_implies_Equation1366 (G : Type*) [Magma G] (h : Equation2217 G) : Equation1366 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK1) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation1378_implies_Equation176 (G : Type*) [Magma G] (h : Equation1378 G) : Equation176 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X4 X5 : G) : (X1 ◇ (X4 ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


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
theorem Equation1801_implies_Equation182 (G : Type*) [Magma G] (h : Equation1801 G) : Equation182 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 X4 X5 : G) : ((X4 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X3) = ((X4 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X3 X4 X5 X6 : G) : ((X4 ◇ X3) ◇ (X5 ◇ X6)) = X6 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2 in 12
  have eq37 (X0 X1 : G) : sK0 ≠ ((X0 ◇ X1) ◇ (sK2 ◇ sK0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq37 eq14


@[equational_result]
theorem Equation182_implies_Equation2217 (G : Type*) [Magma G] (h : Equation182 G) : Equation2217 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK3) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


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
theorem Equation1962_implies_Equation1115 (G : Type*) [Magma G] (h : Equation1962 G) : Equation1115 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X2) ◇ (X3 ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X2 : G) : (X2 ◇ (X2 ◇ X2)) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.1 in 12
  have eq27 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq29 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq35 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).2.2 in 11
  have eq43 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = (X0 ◇ X0) := superpose eq35 eq29 -- backward demodulation 29,35
  have eq44 (X0 X2 : G) : (X0 ◇ X2) = ((X2 ◇ X2) ◇ X2) := superpose eq43 eq27 -- backward demodulation 27,43
  have eq48 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := superpose eq44 eq10 -- backward demodulation 10,44
  have eq49 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq35 eq48 -- forward demodulation 48,35
  have eq51 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq44 eq44 -- superposition 44,44, 44 into 44, unify on (0).2 in 44 and (0).2 in 44
  have eq113 (X0 X2 X3 : G) : (X3 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq51 -- superposition 51,9, 9 into 51, unify on (0).2 in 9 and (0).1 in 51
  have eq143 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ sK0)) := superpose eq51 eq49 -- superposition 49,51, 51 into 49, unify on (0).2 in 51 and (0).2.2 in 49
  subsumption eq143 eq113


@[equational_result]
theorem Equation1767_implies_Equation1125 (G : Type*) [Magma G] (h : Equation1767 G) : Equation1125 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK0)) := mod_symm nh
  have eq11 (X2 X4 X5 : G) : (X2 ◇ ((X4 ◇ X5) ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X0)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq23 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq23 eq15


@[equational_result]
theorem Equation1318_implies_Equation554 (G : Type*) [Magma G] (h : Equation1318 G) : Equation554 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation1318_implies_Equation114 (G : Type*) [Magma G] (h : Equation1318 G) : Equation114 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation1890_implies_Equation2217 (G : Type*) [Magma G] (h : Equation1890 G) : Equation2217 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK3) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X1 X2 : G) : (X2 ◇ X1) = ((X2 ◇ X1) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq30 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq43 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq30 eq30 -- superposition 30,30, 30 into 30, unify on (0).2 in 30 and (0).1.2 in 30
  have eq48 : sK0 ≠ ((sK3 ◇ sK3) ◇ (sK1 ◇ sK0)) := superpose eq43 eq10 -- backward demodulation 10,43
  have eq49 : sK0 ≠ ((sK3 ◇ sK3) ◇ (sK0 ◇ sK0)) := superpose eq43 eq48 -- forward demodulation 48,43
  subsumption eq49 eq30


@[equational_result]
theorem Equation2222_implies_Equation1890 (G : Type*) [Magma G] (h : Equation2222 G) : Equation1890 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation2144_implies_Equation1931 (G : Type*) [Magma G] (h : Equation2144 G) : Equation1931 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation2144_implies_Equation2222 (G : Type*) [Magma G] (h : Equation2144 G) : Equation2222 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK3) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq21 : sK0 ≠ ((sK3 ◇ sK3) ◇ (sK2 ◇ sK0)) := superpose eq16 eq10 -- backward demodulation 10,16
  have eq22 : sK0 ≠ ((sK3 ◇ sK3) ◇ (sK0 ◇ sK0)) := superpose eq16 eq21 -- forward demodulation 21,16
  subsumption eq22 eq12


@[equational_result]
theorem Equation176_implies_Equation2178 (G : Type*) [Magma G] (h : Equation176 G) : Equation2178 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation2130_implies_Equation2144 (G : Type*) [Magma G] (h : Equation2130 G) : Equation2144 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK2) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 X2 X3 : G) : (X2 ◇ X1) = (((X3 ◇ X3) ◇ (X2 ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq27 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq11 eq13 -- superposition 13,11, 11 into 13, unify on (0).2 in 11 and (0).2.1 in 13
  have eq33 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq26 -- forward demodulation 26,11
  have eq35 : sK0 ≠ ((sK2 ◇ sK2) ◇ (sK0 ◇ sK0)) := superpose eq27 eq10 -- backward demodulation 10,27
  subsumption eq35 eq33


@[equational_result]
theorem Equation2140_implies_Equation169 (G : Type*) [Magma G] (h : Equation2140 G) : Equation169 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 X3 : G) : (X1 ◇ X2) = (((X3 ◇ X3) ◇ X3) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq39 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq39 rfl


@[equational_result]
theorem Equation172_implies_Equation2140 (G : Type*) [Magma G] (h : Equation172 G) : Equation2140 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK1) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ X1) = (X1 ◇ (X3 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq19 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK0)) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq20 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := superpose eq15 eq19 -- forward demodulation 19,15
  have eq21 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).1 in 15
  have eq29 (X0 : G) : sK0 ≠ ((sK1 ◇ sK1) ◇ (X0 ◇ sK0)) := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).2.2 in 20
  subsumption eq29 eq21


@[equational_result]
theorem Equation2207_implies_Equation172 (G : Type*) [Magma G] (h : Equation2207 G) : Equation172 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation2207_implies_Equation1344 (G : Type*) [Magma G] (h : Equation2207 G) : Equation1344 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK2) ◇ sK3) ◇ sK0)) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 rfl


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
theorem Equation1332_implies_Equation2107 (G : Type*) [Magma G] (h : Equation1332 G) : Equation2107 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK2) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X3) = (X0 ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X3) = (X0 ◇ X3) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq33 (X0 X3 X4 : G) : (X4 ◇ (X0 ◇ X3)) = X3 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.2 in 11
  have eq49 : sK0 ≠ sK0 := superpose eq33 eq10 -- superposition 10,33, 33 into 10, unify on (0).2 in 33 and (0).2 in 10
  subsumption eq49 rfl


