import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation433_implies_Equation1853 (G : Type*) [Magma G] (h : Equation433 G) : Equation1853 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation433_implies_Equation429 (G : Type*) [Magma G] (h : Equation433 G) : Equation429 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation433_implies_Equation832 (G : Type*) [Magma G] (h : Equation433 G) : Equation832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2.2 in 9
  have eq74 : sK0 ≠ sK0 := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq74 rfl


@[equational_result]
theorem Equation433_implies_Equation1834 (G : Type*) [Magma G] (h : Equation433 G) : Equation1834 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


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
theorem Equation433_implies_Equation1045 (G : Type*) [Magma G] (h : Equation433 G) : Equation1045 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation433_implies_Equation1055 (G : Type*) [Magma G] (h : Equation433 G) : Equation1055 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation433_implies_Equation1234 (G : Type*) [Magma G] (h : Equation433 G) : Equation1234 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation433_implies_Equation3925 (G : Type*) [Magma G] (h : Equation433 G) : Equation3925 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 rfl


@[equational_result]
theorem Equation433_implies_Equation3319 (G : Type*) [Magma G] (h : Equation433 G) : Equation3319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 rfl


@[equational_result]
theorem Equation433_implies_Equation1258 (G : Type*) [Magma G] (h : Equation433 G) : Equation1258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation433_implies_Equation1048 (G : Type*) [Magma G] (h : Equation433 G) : Equation1048 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation433_implies_Equation3255 (G : Type*) [Magma G] (h : Equation433 G) : Equation3255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 rfl


@[equational_result]
theorem Equation433_implies_Equation4316 (G : Type*) [Magma G] (h : Equation433 G) : Equation4316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation433_implies_Equation1262 (G : Type*) [Magma G] (h : Equation433 G) : Equation1262 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation433_implies_Equation843 (G : Type*) [Magma G] (h : Equation433 G) : Equation843 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2.2 in 9
  have eq74 : sK0 ≠ sK0 := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq74 rfl


@[equational_result]
theorem Equation433_implies_Equation823 (G : Type*) [Magma G] (h : Equation433 G) : Equation823 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2.2 in 9
  have eq74 : sK0 ≠ sK0 := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq74 rfl


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
theorem Equation558_implies_Equation588 (G : Type*) [Magma G] (h : Equation558 G) : Equation588 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq31 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2 in 13
  have eq32 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := superpose eq15 eq31 -- forward demodulation 31,15
  subsumption eq32 eq9


@[equational_result]
theorem Equation4537_implies_Equation4677 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK1 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = (((X1 ◇ X3) ◇ X2) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq19 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X1 : G) : (X0 ◇ (sK0 ◇ sK2)) ≠ (X1 ◇ (sK1 ◇ sK2)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1 in 19
  have eq221 (X1 X2 X3 X4 : G) : (X4 ◇ (sK0 ◇ sK2)) ≠ (((X1 ◇ X2) ◇ X3) ◇ sK2) := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).2 in 20
  subsumption eq221 eq15


@[equational_result]
theorem Equation4537_implies_Equation4320 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = (((X1 ◇ X3) ◇ X2) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X4 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq69 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK0 ◇ sK0)) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  have eq79 (X0 X1 : G) : (X0 ◇ (sK1 ◇ sK0)) ≠ (X1 ◇ (sK0 ◇ sK0)) := superpose eq17 eq69 -- superposition 69,17, 17 into 69, unify on (0).2 in 17 and (0).1 in 69
  have eq219 (X1 X2 X3 X4 : G) : (X4 ◇ (sK1 ◇ sK0)) ≠ (((X1 ◇ X2) ◇ X3) ◇ sK0) := superpose eq15 eq79 -- superposition 79,15, 15 into 79, unify on (0).2 in 15 and (0).2 in 79
  subsumption eq219 eq15


@[equational_result]
theorem Equation4537_implies_Equation4378 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4378 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK4 ◇ sK2)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = (((X1 ◇ X3) ◇ X2) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X4 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq69 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK4 ◇ sK2)) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  have eq79 (X0 X1 : G) : (X0 ◇ (sK1 ◇ sK2)) ≠ (X1 ◇ (sK4 ◇ sK2)) := superpose eq17 eq69 -- superposition 69,17, 17 into 69, unify on (0).2 in 17 and (0).1 in 69
  have eq219 (X1 X2 X3 X4 : G) : (X4 ◇ (sK1 ◇ sK2)) ≠ (((X1 ◇ X2) ◇ X3) ◇ sK2) := superpose eq15 eq79 -- superposition 79,15, 15 into 79, unify on (0).2 in 15 and (0).2 in 79
  subsumption eq219 eq15


@[equational_result]
theorem Equation4537_implies_Equation4409 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4409 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X4 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ X1) ◇ sK1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq73 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = ((X3 ◇ (X1 ◇ X2)) ◇ X5) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2.1 in 9
  have eq151 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X2 ◇ (X0 ◇ X1)) ◇ sK1) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2.1 in 20
  subsumption eq151 eq73


@[equational_result]
theorem Equation4537_implies_Equation4559 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4559 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X4 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK3 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ X1) ◇ sK2) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq72 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = ((X3 ◇ (X1 ◇ X2)) ◇ X5) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2.1 in 9
  have eq151 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((X2 ◇ (X0 ◇ X1)) ◇ sK2) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2.1 in 20
  subsumption eq151 eq72


@[equational_result]
theorem Equation4537_implies_Equation4512 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4512 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X4 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ X1) ◇ sK2) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq72 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = ((X3 ◇ (X1 ◇ X2)) ◇ X5) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2.1 in 9
  have eq151 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((X2 ◇ (X0 ◇ X1)) ◇ sK2) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2.1 in 20
  subsumption eq151 eq72


@[equational_result]
theorem Equation4537_implies_Equation4494 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4494 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X4 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ X1) ◇ sK1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq73 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = ((X3 ◇ (X1 ◇ X2)) ◇ X5) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2.1 in 9
  have eq151 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((X2 ◇ (X0 ◇ X1)) ◇ sK1) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2.1 in 20
  subsumption eq151 eq73


@[equational_result]
theorem Equation4537_implies_Equation4464 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4464 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK3) ◇ sK0) := mod_symm nh
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X4 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ X1) ◇ sK0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq72 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = ((X3 ◇ (X1 ◇ X2)) ◇ X5) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2.1 in 9
  have eq151 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((X2 ◇ (X0 ◇ X1)) ◇ sK0) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2.1 in 20
  subsumption eq151 eq72


@[equational_result]
theorem Equation4537_implies_Equation4316 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = (((X1 ◇ X3) ◇ X2) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X4 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq69 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ sK0)) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  have eq79 (X0 X1 : G) : (X0 ◇ (sK1 ◇ sK0)) ≠ (X1 ◇ (sK2 ◇ sK0)) := superpose eq17 eq69 -- superposition 69,17, 17 into 69, unify on (0).2 in 17 and (0).1 in 69
  have eq219 (X1 X2 X3 X4 : G) : (X4 ◇ (sK1 ◇ sK0)) ≠ (((X1 ◇ X2) ◇ X3) ◇ sK0) := superpose eq15 eq79 -- superposition 79,15, 15 into 79, unify on (0).2 in 15 and (0).2 in 79
  subsumption eq219 eq15


@[equational_result]
theorem Equation4537_implies_Equation4412 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4412 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X4 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ X1) ◇ sK1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq72 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = ((X3 ◇ (X1 ◇ X2)) ◇ X5) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2.1 in 9
  have eq151 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X2 ◇ (X0 ◇ X1)) ◇ sK1) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2.1 in 20
  subsumption eq151 eq72


@[equational_result]
theorem Equation4537_implies_Equation4520 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4520 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X4 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ X1) ◇ sK2) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq72 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = ((X3 ◇ (X1 ◇ X2)) ◇ X5) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2.1 in 9
  have eq151 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((X2 ◇ (X0 ◇ X1)) ◇ sK2) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2.1 in 20
  subsumption eq151 eq72


@[equational_result]
theorem Equation4537_implies_Equation4460 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4460 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X4 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ X1) ◇ sK0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq72 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = ((X3 ◇ (X1 ◇ X2)) ◇ X5) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2.1 in 9
  have eq151 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((X2 ◇ (X0 ◇ X1)) ◇ sK0) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2.1 in 20
  subsumption eq151 eq72


@[equational_result]
theorem Equation4537_implies_Equation4611 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4611 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = (((X1 ◇ X3) ◇ X2) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq19 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X1 : G) : (X0 ◇ (sK0 ◇ sK1)) ≠ (X1 ◇ (sK1 ◇ sK1)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1 in 19
  have eq221 (X1 X2 X3 X4 : G) : (X4 ◇ (sK0 ◇ sK1)) ≠ (((X1 ◇ X2) ◇ X3) ◇ sK1) := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).2 in 20
  subsumption eq221 eq15


@[equational_result]
theorem Equation4537_implies_Equation4642 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4642 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK2 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = (((X1 ◇ X3) ◇ X2) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq19 (X0 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (X0 ◇ (sK2 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X1 : G) : (X0 ◇ (sK0 ◇ sK0)) ≠ (X1 ◇ (sK2 ◇ sK0)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1 in 19
  have eq221 (X1 X2 X3 X4 : G) : (X4 ◇ (sK0 ◇ sK0)) ≠ (((X1 ◇ X2) ◇ X3) ◇ sK0) := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).2 in 20
  subsumption eq221 eq15


@[equational_result]
theorem Equation4537_implies_Equation4406 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4406 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X4 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ X1) ◇ sK1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq72 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = ((X3 ◇ (X1 ◇ X2)) ◇ X5) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2.1 in 9
  have eq151 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X2 ◇ (X0 ◇ X1)) ◇ sK1) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2.1 in 20
  subsumption eq151 eq72


@[equational_result]
theorem Equation4537_implies_Equation4502 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4502 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ sK1) := mod_symm nh
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X4 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ X1) ◇ sK1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq72 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = ((X3 ◇ (X1 ◇ X2)) ◇ X5) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2.1 in 9
  have eq151 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((X2 ◇ (X0 ◇ X1)) ◇ sK1) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2.1 in 20
  subsumption eq151 eq72


@[equational_result]
theorem Equation4537_implies_Equation4284 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = (((X1 ◇ X3) ◇ X2) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X4 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq69 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  have eq79 (X0 X1 : G) : (X0 ◇ (sK0 ◇ sK1)) ≠ (X1 ◇ (sK1 ◇ sK1)) := superpose eq17 eq69 -- superposition 69,17, 17 into 69, unify on (0).2 in 17 and (0).1 in 69
  have eq219 (X1 X2 X3 X4 : G) : (X4 ◇ (sK0 ◇ sK1)) ≠ (((X1 ◇ X2) ◇ X3) ◇ sK1) := superpose eq15 eq79 -- superposition 79,15, 15 into 79, unify on (0).2 in 15 and (0).2 in 79
  subsumption eq219 eq15


@[equational_result]
theorem Equation4537_implies_Equation4473 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4473 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X4 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ X1) ◇ sK1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq73 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = ((X3 ◇ (X1 ◇ X2)) ◇ X5) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2.1 in 9
  have eq151 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((X2 ◇ (X0 ◇ X1)) ◇ sK1) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2.1 in 20
  subsumption eq151 eq73


@[equational_result]
theorem Equation4537_implies_Equation4516 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4516 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X4 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ X1) ◇ sK2) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq73 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = ((X3 ◇ (X1 ◇ X2)) ◇ X5) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2.1 in 9
  have eq151 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((X2 ◇ (X0 ◇ X1)) ◇ sK2) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2.1 in 20
  subsumption eq151 eq73


@[equational_result]
theorem Equation4537_implies_Equation4622 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4622 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = (((X1 ◇ X3) ◇ X2) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq19 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ (X0 ◇ (sK2 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X1 : G) : (X0 ◇ (sK0 ◇ sK1)) ≠ (X1 ◇ (sK2 ◇ sK1)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1 in 19
  have eq221 (X1 X2 X3 X4 : G) : (X4 ◇ (sK0 ◇ sK1)) ≠ (((X1 ◇ X2) ◇ X3) ◇ sK1) := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).2 in 20
  subsumption eq221 eq15


@[equational_result]
theorem Equation4537_implies_Equation4579 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4579 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK4) ◇ sK2) := mod_symm nh
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X4 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK3 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ X1) ◇ sK2) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq72 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = ((X3 ◇ (X1 ◇ X2)) ◇ X5) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2.1 in 9
  have eq151 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((X2 ◇ (X0 ◇ X1)) ◇ sK2) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2.1 in 20
  subsumption eq151 eq72


@[equational_result]
theorem Equation4537_implies_Equation4307 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = (((X1 ◇ X3) ◇ X2) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X4 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq61 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK1)) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  have eq79 (X0 X1 : G) : (X0 ◇ (sK0 ◇ sK1)) ≠ (X1 ◇ (sK2 ◇ sK1)) := superpose eq17 eq61 -- superposition 61,17, 17 into 61, unify on (0).2 in 17 and (0).1 in 61
  have eq219 (X1 X2 X3 X4 : G) : (X4 ◇ (sK0 ◇ sK1)) ≠ (((X1 ◇ X2) ◇ X3) ◇ sK1) := superpose eq15 eq79 -- superposition 79,15, 15 into 79, unify on (0).2 in 15 and (0).2 in 79
  subsumption eq219 eq15


@[equational_result]
theorem Equation4537_implies_Equation4435 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4435 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X4 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK0 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ X1) ◇ sK0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq72 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = ((X3 ◇ (X1 ◇ X2)) ◇ X5) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2.1 in 9
  have eq151 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((X2 ◇ (X0 ◇ X1)) ◇ sK0) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2.1 in 20
  subsumption eq151 eq72


@[equational_result]
theorem Equation4537_implies_Equation4574 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4574 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X4 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK3 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ X1) ◇ sK2) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq72 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = ((X3 ◇ (X1 ◇ X2)) ◇ X5) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2.1 in 9
  have eq151 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((X2 ◇ (X0 ◇ X1)) ◇ sK2) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2.1 in 20
  subsumption eq151 eq72


@[equational_result]
theorem Equation4537_implies_Equation4304 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4304 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = (((X1 ◇ X3) ◇ X2) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X4 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq69 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  have eq79 (X0 X1 : G) : (X0 ◇ (sK0 ◇ sK1)) ≠ (X1 ◇ (sK1 ◇ sK1)) := superpose eq17 eq69 -- superposition 69,17, 17 into 69, unify on (0).2 in 17 and (0).1 in 69
  have eq219 (X1 X2 X3 X4 : G) : (X4 ◇ (sK0 ◇ sK1)) ≠ (((X1 ◇ X2) ◇ X3) ◇ sK1) := superpose eq15 eq79 -- superposition 79,15, 15 into 79, unify on (0).2 in 15 and (0).2 in 79
  subsumption eq219 eq15


@[equational_result]
theorem Equation4537_implies_Equation4470 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4470 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X4 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ X1) ◇ sK1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq72 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = ((X3 ◇ (X1 ◇ X2)) ◇ X5) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2.1 in 9
  have eq151 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((X2 ◇ (X0 ◇ X1)) ◇ sK1) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2.1 in 20
  subsumption eq151 eq72


@[equational_result]
theorem Equation4537_implies_Equation4420 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4420 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X4 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ X1) ◇ sK1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq73 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = ((X3 ◇ (X1 ◇ X2)) ◇ X5) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2.1 in 9
  have eq151 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X2 ◇ (X0 ◇ X1)) ◇ sK1) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2.1 in 20
  subsumption eq151 eq73


@[equational_result]
theorem Equation4537_implies_Equation4362 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4362 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = (((X1 ◇ X3) ◇ X2) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X4 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq69 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK0 ◇ sK2)) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  have eq79 (X0 X1 : G) : (X0 ◇ (sK1 ◇ sK2)) ≠ (X1 ◇ (sK0 ◇ sK2)) := superpose eq17 eq69 -- superposition 69,17, 17 into 69, unify on (0).2 in 17 and (0).1 in 69
  have eq219 (X1 X2 X3 X4 : G) : (X4 ◇ (sK1 ◇ sK2)) ≠ (((X1 ◇ X2) ◇ X3) ◇ sK2) := superpose eq15 eq79 -- superposition 79,15, 15 into 79, unify on (0).2 in 15 and (0).2 in 79
  subsumption eq219 eq15


@[equational_result]
theorem Equation3919_implies_Equation4130 (G : Type*) [Magma G] (h : Equation3919 G) : Equation4130 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation3919_implies_Equation4398 (G : Type*) [Magma G] (h : Equation3919 G) : Equation4398 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq30 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq30 rfl


@[equational_result]
theorem Equation3919_implies_Equation4381 (G : Type*) [Magma G] (h : Equation3919 G) : Equation4381 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq30 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq30 rfl


@[equational_result]
theorem Equation3919_implies_Equation3512 (G : Type*) [Magma G] (h : Equation3919 G) : Equation3512 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq28 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq28 rfl


@[equational_result]
theorem Equation3919_implies_Equation307 (G : Type*) [Magma G] (h : Equation3919 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1 in 8
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq8 eq10 -- forward demodulation 10,8
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2 in 12
  have eq26 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2 in 9
  subsumption eq26 rfl


@[equational_result]
theorem Equation3919_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3919 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1 in 8
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq8 eq10 -- forward demodulation 10,8
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2 in 12
  have eq21 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq16 eq9 -- backward demodulation 9,16
  subsumption eq21 eq16


@[equational_result]
theorem Equation3919_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3919 G) : Equation3456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1 in 8
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq8 eq10 -- forward demodulation 10,8
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq9 -- backward demodulation 9,12
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2 in 12
  have eq27 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq17 eq13 -- superposition 13,17, 17 into 13, unify on (0).2 in 17 and (0).2 in 13
  subsumption eq27 rfl


@[equational_result]
theorem Equation3919_implies_Equation3729 (G : Type*) [Magma G] (h : Equation3919 G) : Equation3729 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3919_implies_Equation379 (G : Type*) [Magma G] (h : Equation3919 G) : Equation379 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3919_implies_Equation3457 (G : Type*) [Magma G] (h : Equation3919 G) : Equation3457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq30 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq30 rfl


@[equational_result]
theorem Equation3919_implies_Equation4128 (G : Type*) [Magma G] (h : Equation3919 G) : Equation4128 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation3919_implies_Equation4136 (G : Type*) [Magma G] (h : Equation3919 G) : Equation4136 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK3) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation3919_implies_Equation3728 (G : Type*) [Magma G] (h : Equation3919 G) : Equation3728 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq20 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation3919_implies_Equation3727 (G : Type*) [Magma G] (h : Equation3919 G) : Equation3727 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3919_implies_Equation323 (G : Type*) [Magma G] (h : Equation3919 G) : Equation323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq27 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq27 rfl


@[equational_result]
theorem Equation3919_implies_Equation3724 (G : Type*) [Magma G] (h : Equation3919 G) : Equation3724 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3919_implies_Equation377 (G : Type*) [Magma G] (h : Equation3919 G) : Equation377 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3919_implies_Equation378 (G : Type*) [Magma G] (h : Equation3919 G) : Equation378 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq21 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation3919_implies_Equation4127 (G : Type*) [Magma G] (h : Equation3919 G) : Equation4127 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation3919_implies_Equation4399 (G : Type*) [Magma G] (h : Equation3919 G) : Equation4399 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq28 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq28 rfl


@[equational_result]
theorem Equation3919_implies_Equation3511 (G : Type*) [Magma G] (h : Equation3919 G) : Equation3511 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq30 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq30 rfl


@[equational_result]
theorem Equation3919_implies_Equation3513 (G : Type*) [Magma G] (h : Equation3919 G) : Equation3513 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq30 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq30 rfl


@[equational_result]
theorem Equation3919_implies_Equation4400 (G : Type*) [Magma G] (h : Equation3919 G) : Equation4400 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq30 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq30 rfl


@[equational_result]
theorem Equation222_implies_Equation4435 (G : Type*) [Magma G] (h : Equation222 G) : Equation4435 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation222_implies_Equation118 (G : Type*) [Magma G] (h : Equation222 G) : Equation118 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq20 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation222_implies_Equation99 (G : Type*) [Magma G] (h : Equation222 G) : Equation99 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq10 eq9 -- backward demodulation 9,10
  have eq14 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2 in 10
  have eq19 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq14 -- superposition 14,10, 10 into 14, unify on (0).2 in 10 and (0).1.2 in 14
  have eq32 : sK0 ≠ sK0 := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).2 in 11
  subsumption eq32 rfl


@[equational_result]
theorem Equation222_implies_Equation274 (G : Type*) [Magma G] (h : Equation222 G) : Equation274 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq12 eq9


@[equational_result]
theorem Equation1030_implies_Equation417 (G : Type*) [Magma G] (h : Equation1030 G) : Equation417 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


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
theorem Equation1030_implies_Equation1024 (G : Type*) [Magma G] (h : Equation1030 G) : Equation1024 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK2)) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation1030_implies_Equation3458 (G : Type*) [Magma G] (h : Equation1030 G) : Equation3458 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq17 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq18 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq18 eq17


@[equational_result]
theorem Equation1030_implies_Equation828 (G : Type*) [Magma G] (h : Equation1030 G) : Equation828 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq17 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq23 : sK0 ≠ sK0 := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq23 rfl


@[equational_result]
theorem Equation1030_implies_Equation822 (G : Type*) [Magma G] (h : Equation1030 G) : Equation822 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq17 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq18 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq18 eq17


@[equational_result]
theorem Equation1030_implies_Equation1033 (G : Type*) [Magma G] (h : Equation1030 G) : Equation1033 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq17 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq23 : sK0 ≠ sK0 := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq23 rfl


@[equational_result]
theorem Equation1030_implies_Equation829 (G : Type*) [Magma G] (h : Equation1030 G) : Equation829 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq17 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq22 : sK0 ≠ sK0 := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation1030_implies_Equation3257 (G : Type*) [Magma G] (h : Equation1030 G) : Equation3257 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq20 : sK0 ≠ sK0 := superpose eq14 eq13 -- superposition 13,14, 14 into 13, unify on (0).2 in 14 and (0).2 in 13
  subsumption eq20 rfl


@[equational_result]
theorem Equation2658_implies_Equation2669 (G : Type*) [Magma G] (h : Equation2658 G) : Equation2669 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq13 eq14 -- forward demodulation 14,13
  subsumption eq15 eq9


@[equational_result]
theorem Equation2658_implies_Equation2045 (G : Type*) [Magma G] (h : Equation2658 G) : Equation2045 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (((X4 ◇ X4) ◇ X0) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq12


@[equational_result]
theorem Equation2658_implies_Equation3467 (G : Type*) [Magma G] (h : Equation2658 G) : Equation3467 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation2658_implies_Equation2863 (G : Type*) [Magma G] (h : Equation2658 G) : Equation2863 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (((X4 ◇ X4) ◇ X0) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq12


@[equational_result]
theorem Equation2658_implies_Equation3321 (G : Type*) [Magma G] (h : Equation2658 G) : Equation3321 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation2658_implies_Equation264 (G : Type*) [Magma G] (h : Equation2658 G) : Equation264 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (((X4 ◇ X4) ◇ X0) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq12


@[equational_result]
theorem Equation2658_implies_Equation3267 (G : Type*) [Magma G] (h : Equation2658 G) : Equation3267 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq13 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation2658_implies_Equation3266 (G : Type*) [Magma G] (h : Equation2658 G) : Equation3266 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq13 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation4407_implies_Equation4417 (G : Type*) [Magma G] (h : Equation4407 G) : Equation4417 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq31 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK0) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq67 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X4) = (X3 ◇ (X3 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq183 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq16 eq31 -- superposition 31,16, 16 into 31, unify on (0).2 in 16 and (0).2 in 31
  subsumption eq183 eq67


@[equational_result]
theorem Equation4407_implies_Equation4402 (G : Type*) [Magma G] (h : Equation4407 G) : Equation4402 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq31 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq67 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X4) = (X3 ◇ (X3 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq183 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq16 eq31 -- superposition 31,16, 16 into 31, unify on (0).2 in 16 and (0).2 in 31
  subsumption eq183 eq67


@[equational_result]
theorem Equation4407_implies_Equation4385 (G : Type*) [Magma G] (h : Equation4407 G) : Equation4385 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq35 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK0) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq67 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X4) = (X3 ◇ (X3 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq177 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq16 eq35 -- superposition 35,16, 16 into 35, unify on (0).2 in 16 and (0).2 in 35
  subsumption eq177 eq67


@[equational_result]
theorem Equation4407_implies_Equation4404 (G : Type*) [Magma G] (h : Equation4407 G) : Equation4404 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq31 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq67 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X4) = (X3 ◇ (X3 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq183 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq16 eq31 -- superposition 31,16, 16 into 31, unify on (0).2 in 16 and (0).2 in 31
  subsumption eq183 eq67


@[equational_result]
theorem Equation4407_implies_Equation4384 (G : Type*) [Magma G] (h : Equation4407 G) : Equation4384 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq31 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq67 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X4) = (X3 ◇ (X3 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq183 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq16 eq31 -- superposition 31,16, 16 into 31, unify on (0).2 in 16 and (0).2 in 31
  subsumption eq183 eq67


@[equational_result]
theorem Equation4407_implies_Equation4416 (G : Type*) [Magma G] (h : Equation4407 G) : Equation4416 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq31 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK0) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq67 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X4) = (X3 ◇ (X3 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq183 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq16 eq31 -- superposition 31,16, 16 into 31, unify on (0).2 in 16 and (0).2 in 31
  subsumption eq183 eq67


@[equational_result]
theorem Equation4407_implies_Equation4408 (G : Type*) [Magma G] (h : Equation4407 G) : Equation4408 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq31 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq67 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X4) = (X3 ◇ (X3 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq174 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq16 eq31 -- superposition 31,16, 16 into 31, unify on (0).2 in 16 and (0).2 in 31
  subsumption eq174 eq67


@[equational_result]
theorem Equation4407_implies_Equation4426 (G : Type*) [Magma G] (h : Equation4407 G) : Equation4426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq31 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq67 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X4) = (X3 ◇ (X3 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq174 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq16 eq31 -- superposition 31,16, 16 into 31, unify on (0).2 in 16 and (0).2 in 31
  subsumption eq174 eq67


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
theorem Equation4407_implies_Equation4420 (G : Type*) [Magma G] (h : Equation4407 G) : Equation4420 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq35 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK1) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq67 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X4) = (X3 ◇ (X3 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq177 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq16 eq35 -- superposition 35,16, 16 into 35, unify on (0).2 in 16 and (0).2 in 35
  subsumption eq177 eq67


@[equational_result]
theorem Equation4407_implies_Equation4419 (G : Type*) [Magma G] (h : Equation4407 G) : Equation4419 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq31 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK1) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq67 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X4) = (X3 ◇ (X3 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq183 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq16 eq31 -- superposition 31,16, 16 into 31, unify on (0).2 in 16 and (0).2 in 31
  subsumption eq183 eq67


@[equational_result]
theorem Equation4407_implies_Equation4413 (G : Type*) [Magma G] (h : Equation4407 G) : Equation4413 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq35 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK2) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq67 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X4) = (X3 ◇ (X3 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq177 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq16 eq35 -- superposition 35,16, 16 into 35, unify on (0).2 in 16 and (0).2 in 35
  subsumption eq177 eq67


@[equational_result]
theorem Equation4407_implies_Equation4383 (G : Type*) [Magma G] (h : Equation4407 G) : Equation4383 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq35 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq67 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X4) = (X3 ◇ (X3 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq177 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq16 eq35 -- superposition 35,16, 16 into 35, unify on (0).2 in 16 and (0).2 in 35
  subsumption eq177 eq67


@[equational_result]
theorem Equation4407_implies_Equation4430 (G : Type*) [Magma G] (h : Equation4407 G) : Equation4430 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq35 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq67 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X4) = (X3 ◇ (X3 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq177 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq16 eq35 -- superposition 35,16, 16 into 35, unify on (0).2 in 16 and (0).2 in 35
  subsumption eq177 eq67


@[equational_result]
theorem Equation4407_implies_Equation4424 (G : Type*) [Magma G] (h : Equation4407 G) : Equation4424 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq31 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq67 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X4) = (X3 ◇ (X3 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq174 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq16 eq31 -- superposition 31,16, 16 into 31, unify on (0).2 in 16 and (0).2 in 31
  subsumption eq174 eq67


@[equational_result]
theorem Equation4407_implies_Equation4276 (G : Type*) [Magma G] (h : Equation4407 G) : Equation4276 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq57 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ X2) ◇ X3) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq451 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X3 ◇ (X3 ◇ X2)) := superpose eq14 eq57 -- superposition 57,14, 14 into 57, unify on (0).2 in 14 and (0).2 in 57
  have eq1113 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq451 eq10 -- superposition 10,451, 451 into 10, unify on (0).2 in 451 and (0).2 in 10
  subsumption eq1113 eq451


@[equational_result]
theorem Equation4407_implies_Equation4293 (G : Type*) [Magma G] (h : Equation4407 G) : Equation4293 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq57 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ X2) ◇ X3) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq451 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X3 ◇ (X3 ◇ X2)) := superpose eq14 eq57 -- superposition 57,14, 14 into 57, unify on (0).2 in 14 and (0).2 in 57
  have eq1113 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq451 eq10 -- superposition 10,451, 451 into 10, unify on (0).2 in 451 and (0).2 in 10
  subsumption eq1113 eq451


@[equational_result]
theorem Equation1312_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1312 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2.1 in 10
  have eq15 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq8 eq11 -- forward demodulation 11,8
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2 in 8
  have eq23 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq17 eq9 -- backward demodulation 9,17
  subsumption eq23 eq17


@[equational_result]
theorem Equation1312_implies_Equation2035 (G : Type*) [Magma G] (h : Equation1312 G) : Equation2035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2.1 in 10
  have eq15 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq8 eq11 -- forward demodulation 11,8
  have eq21 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1.1 in 8
  have eq26 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq15 eq21 -- forward demodulation 21,15
  have eq80 : sK0 ≠ sK0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).2 in 9
  subsumption eq80 rfl


@[equational_result]
theorem Equation1312_implies_Equation411 (G : Type*) [Magma G] (h : Equation1312 G) : Equation411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2.1 in 10
  have eq15 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq8 eq11 -- forward demodulation 11,8
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2 in 8
  have eq23 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq17 eq9 -- backward demodulation 9,17
  subsumption eq23 eq17


@[equational_result]
theorem Equation1312_implies_Equation3862 (G : Type*) [Magma G] (h : Equation1312 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2.1 in 10
  have eq15 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq8 eq11 -- forward demodulation 11,8
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2 in 8
  have eq23 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq17 eq9 -- backward demodulation 9,17
  subsumption eq23 rfl


@[equational_result]
theorem Equation1312_implies_Equation4065 (G : Type*) [Magma G] (h : Equation1312 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2.1 in 10
  have eq15 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq8 eq11 -- forward demodulation 11,8
  have eq22 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).2 in 9
  subsumption eq22 rfl


@[equational_result]
theorem Equation1312_implies_Equation3915 (G : Type*) [Magma G] (h : Equation1312 G) : Equation3915 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.1 in 11
  have eq16 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).1.2 in 9
  have eq24 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq10 -- backward demodulation 10,18
  subsumption eq24 rfl


@[equational_result]
theorem Equation1312_implies_Equation3253 (G : Type*) [Magma G] (h : Equation1312 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2.1 in 10
  have eq15 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq8 eq11 -- forward demodulation 11,8
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2 in 8
  have eq23 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq17 eq9 -- backward demodulation 9,17
  subsumption eq23 rfl


@[equational_result]
theorem Equation1312_implies_Equation3319 (G : Type*) [Magma G] (h : Equation1312 G) : Equation3319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.1 in 11
  have eq16 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).1.2 in 9
  have eq24 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq10 -- backward demodulation 10,18
  subsumption eq24 rfl


@[equational_result]
theorem Equation1312_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1312 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2.1 in 10
  have eq15 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq8 eq11 -- forward demodulation 11,8
  have eq19 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1 in 8
  have eq52 : sK0 ≠ sK0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2 in 9
  subsumption eq52 rfl


@[equational_result]
theorem Equation1312_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1312 G) : Equation1020 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2.1 in 10
  have eq15 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq8 eq11 -- forward demodulation 11,8
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2 in 8
  have eq23 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq17 eq9 -- backward demodulation 9,17
  subsumption eq23 eq17


@[equational_result]
theorem Equation1312_implies_Equation8 (G : Type*) [Magma G] (h : Equation1312 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2.1 in 10
  have eq15 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq8 eq11 -- forward demodulation 11,8
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2 in 8
  have eq27 : sK0 ≠ sK0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2 in 9
  subsumption eq27 rfl


@[equational_result]
theorem Equation649_implies_Equation819 (G : Type*) [Magma G] (h : Equation649 G) : Equation819 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X3 ◇ X0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq21 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) = ((X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq37 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X0) = ((X3 ◇ X0) ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq56 (X0 X3 : G) : (X3 ◇ X0) = ((X3 ◇ X0) ◇ X0) := superpose eq9 eq37 -- superposition 37,9, 9 into 37, unify on (0).2 in 9 and (0).2.2 in 37
  have eq71 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := superpose eq56 eq9 -- backward demodulation 9,56
  have eq89 : sK0 ≠ sK0 := superpose eq71 eq10 -- superposition 10,71, 71 into 10, unify on (0).2 in 71 and (0).2 in 10
  subsumption eq89 rfl


@[equational_result]
theorem Equation649_implies_Equation58 (G : Type*) [Magma G] (h : Equation649 G) : Equation58 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X3 ◇ X0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq21 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) = ((X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq37 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X0) = ((X3 ◇ X0) ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq56 (X0 X3 : G) : (X3 ◇ X0) = ((X3 ◇ X0) ◇ X0) := superpose eq9 eq37 -- superposition 37,9, 9 into 37, unify on (0).2 in 9 and (0).2.2 in 37
  have eq71 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := superpose eq56 eq9 -- backward demodulation 9,56
  have eq89 : sK0 ≠ sK0 := superpose eq71 eq10 -- superposition 10,71, 71 into 10, unify on (0).2 in 71 and (0).2 in 10
  subsumption eq89 rfl


@[equational_result]
theorem Equation649_implies_Equation828 (G : Type*) [Magma G] (h : Equation649 G) : Equation828 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X3 ◇ X0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq21 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) = ((X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq37 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X0) = ((X3 ◇ X0) ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq56 (X0 X3 : G) : (X3 ◇ X0) = ((X3 ◇ X0) ◇ X0) := superpose eq9 eq37 -- superposition 37,9, 9 into 37, unify on (0).2 in 9 and (0).2.2 in 37
  have eq71 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := superpose eq56 eq9 -- backward demodulation 9,56
  have eq89 : sK0 ≠ sK0 := superpose eq71 eq10 -- superposition 10,71, 71 into 10, unify on (0).2 in 71 and (0).2 in 10
  subsumption eq89 rfl


@[equational_result]
theorem Equation649_implies_Equation657 (G : Type*) [Magma G] (h : Equation649 G) : Equation657 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X3 ◇ X0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq21 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) = ((X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq37 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X0) = ((X3 ◇ X0) ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq56 (X0 X3 : G) : (X3 ◇ X0) = ((X3 ◇ X0) ◇ X0) := superpose eq9 eq37 -- superposition 37,9, 9 into 37, unify on (0).2 in 9 and (0).2.2 in 37
  have eq71 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := superpose eq56 eq9 -- backward demodulation 9,56
  have eq89 : sK0 ≠ sK0 := superpose eq71 eq10 -- superposition 10,71, 71 into 10, unify on (0).2 in 71 and (0).2 in 10
  subsumption eq89 rfl


@[equational_result]
theorem Equation649_implies_Equation635 (G : Type*) [Magma G] (h : Equation649 G) : Equation635 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X3 ◇ X0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq21 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) = ((X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq37 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X0) = ((X3 ◇ X0) ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq56 (X0 X3 : G) : (X3 ◇ X0) = ((X3 ◇ X0) ◇ X0) := superpose eq9 eq37 -- superposition 37,9, 9 into 37, unify on (0).2 in 9 and (0).2.2 in 37
  have eq71 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := superpose eq56 eq9 -- backward demodulation 9,56
  have eq89 : sK0 ≠ sK0 := superpose eq71 eq10 -- superposition 10,71, 71 into 10, unify on (0).2 in 71 and (0).2 in 10
  subsumption eq89 rfl


@[equational_result]
theorem Equation649_implies_Equation642 (G : Type*) [Magma G] (h : Equation649 G) : Equation642 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X3 ◇ X0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq21 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) = ((X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq37 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X0) = ((X3 ◇ X0) ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq56 (X0 X3 : G) : (X3 ◇ X0) = ((X3 ◇ X0) ◇ X0) := superpose eq9 eq37 -- superposition 37,9, 9 into 37, unify on (0).2 in 9 and (0).2.2 in 37
  have eq71 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := superpose eq56 eq9 -- backward demodulation 9,56
  have eq89 : sK0 ≠ sK0 := superpose eq71 eq10 -- superposition 10,71, 71 into 10, unify on (0).2 in 71 and (0).2 in 10
  subsumption eq89 rfl


@[equational_result]
theorem Equation649_implies_Equation661 (G : Type*) [Magma G] (h : Equation649 G) : Equation661 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK3) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X3 ◇ X0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq21 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) = ((X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq37 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X0) = ((X3 ◇ X0) ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq56 (X0 X3 : G) : (X3 ◇ X0) = ((X3 ◇ X0) ◇ X0) := superpose eq9 eq37 -- superposition 37,9, 9 into 37, unify on (0).2 in 9 and (0).2.2 in 37
  have eq71 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := superpose eq56 eq9 -- backward demodulation 9,56
  have eq89 : sK0 ≠ sK0 := superpose eq71 eq10 -- superposition 10,71, 71 into 10, unify on (0).2 in 71 and (0).2 in 10
  subsumption eq89 rfl


@[equational_result]
theorem Equation3583_implies_Equation359 (G : Type*) [Magma G] (h : Equation3583 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.2 in 8
  have eq12 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq8 eq11 -- forward demodulation 11,8
  have eq16 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2 in 12
  have eq26 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2 in 9
  subsumption eq26 rfl


@[equational_result]
theorem Equation3583_implies_Equation3316 (G : Type*) [Magma G] (h : Equation3583 G) : Equation3316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation3583_implies_Equation4396 (G : Type*) [Magma G] (h : Equation3583 G) : Equation4396 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : ((sK0 ◇ sK0) ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq26 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).1 in 15
  subsumption eq26 rfl


@[equational_result]
theorem Equation3583_implies_Equation3769 (G : Type*) [Magma G] (h : Equation3583 G) : Equation3769 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq20 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation3583_implies_Equation4529 (G : Type*) [Magma G] (h : Equation3583 G) : Equation4529 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK1 ◇ sK2) ≠ ((sK1 ◇ sK1) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq26 : (sK1 ◇ sK2) ≠ (sK1 ◇ sK2) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).2 in 15
  subsumption eq26 rfl


@[equational_result]
theorem Equation3583_implies_Equation3306 (G : Type*) [Magma G] (h : Equation3583 G) : Equation3306 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation3583_implies_Equation3343 (G : Type*) [Magma G] (h : Equation3583 G) : Equation3343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation3583_implies_Equation333 (G : Type*) [Magma G] (h : Equation3583 G) : Equation333 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq21 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation3583_implies_Equation3786 (G : Type*) [Magma G] (h : Equation3583 G) : Equation3786 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq20 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation3583_implies_Equation3326 (G : Type*) [Magma G] (h : Equation3583 G) : Equation3326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation3583_implies_Equation3877 (G : Type*) [Magma G] (h : Equation3583 G) : Equation3877 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq26 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).2 in 15
  subsumption eq26 rfl


@[equational_result]
theorem Equation3583_implies_Equation375 (G : Type*) [Magma G] (h : Equation3583 G) : Equation375 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq17 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq25 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq25 rfl


@[equational_result]
theorem Equation3583_implies_Equation3759 (G : Type*) [Magma G] (h : Equation3583 G) : Equation3759 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3583_implies_Equation4445 (G : Type*) [Magma G] (h : Equation3583 G) : Equation4445 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK1 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq26 : (sK1 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).2 in 15
  subsumption eq26 rfl


@[equational_result]
theorem Equation3583_implies_Equation3749 (G : Type*) [Magma G] (h : Equation3583 G) : Equation3749 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq20 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation3583_implies_Equation3431 (G : Type*) [Magma G] (h : Equation3583 G) : Equation3431 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation3583_implies_Equation3989 (G : Type*) [Magma G] (h : Equation3583 G) : Equation3989 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq26 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).2 in 15
  subsumption eq26 rfl


@[equational_result]
theorem Equation3583_implies_Equation3915 (G : Type*) [Magma G] (h : Equation3583 G) : Equation3915 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq26 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).2 in 15
  subsumption eq26 rfl


@[equational_result]
theorem Equation3583_implies_Equation3837 (G : Type*) [Magma G] (h : Equation3583 G) : Equation3837 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK3) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq20 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation3583_implies_Equation3732 (G : Type*) [Magma G] (h : Equation3583 G) : Equation3732 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3583_implies_Equation323 (G : Type*) [Magma G] (h : Equation3583 G) : Equation323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3583_implies_Equation343 (G : Type*) [Magma G] (h : Equation3583 G) : Equation343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq21 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation3681_implies_Equation3685 (G : Type*) [Magma G] (h : Equation3681 G) : Equation3685 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X1)) = ((X3 ◇ X0) ◇ (X4 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X2 ◇ X0)) = ((X1 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X0 ◇ X3) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq63 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X4) = ((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X3))) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq121 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ sK1) ◇ (X1 ◇ X0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq132 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ X5) = (((X2 ◇ X0) ◇ (X5 ◇ X5)) ◇ ((X3 ◇ X1) ◇ (X4 ◇ X3))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.2 in 12
  have eq149 (X0 X1 X2 X3 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ sK1) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X3))) := superpose eq16 eq121 -- superposition 121,16, 16 into 121, unify on (0).2 in 16 and (0).2.2 in 121
  have eq169 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X3)) = ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X4 ◇ X0) ◇ (X5 ◇ X4))) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2.1 in 15
  have eq243 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X3)) := superpose eq132 eq169 -- forward demodulation 169,132
  have eq247 (X0 X3 X4 : G) : (X4 ◇ X4) = ((X0 ◇ X4) ◇ (X3 ◇ X3)) := superpose eq243 eq63 -- backward demodulation 63,243
  have eq251 (X0 X3 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ sK1) ◇ (X3 ◇ X3)) := superpose eq243 eq149 -- backward demodulation 149,243
  have eq445 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X2 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq247 eq14 -- superposition 14,247, 247 into 14, unify on (0).2 in 247 and (0).2 in 14
  have eq767 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq14 eq251 -- superposition 251,14, 14 into 251, unify on (0).2 in 14 and (0).2 in 251
  subsumption eq767 eq445


@[equational_result]
theorem Equation3681_implies_Equation3707 (G : Type*) [Magma G] (h : Equation3681 G) : Equation3707 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X1)) = ((X3 ◇ X0) ◇ (X4 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X2 ◇ X0)) = ((X1 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X0 ◇ X3) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq63 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X4) = ((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X3))) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq121 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ sK2) ◇ (X1 ◇ X0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq133 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ X5) = (((X2 ◇ X0) ◇ (X5 ◇ X5)) ◇ ((X3 ◇ X1) ◇ (X4 ◇ X3))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.2 in 12
  have eq149 (X0 X1 X2 X3 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ sK2) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X3))) := superpose eq16 eq121 -- superposition 121,16, 16 into 121, unify on (0).2 in 16 and (0).2.2 in 121
  have eq169 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X3)) = ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X4 ◇ X0) ◇ (X5 ◇ X4))) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2.1 in 15
  have eq243 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X3)) := superpose eq133 eq169 -- forward demodulation 169,133
  have eq247 (X0 X3 X4 : G) : (X4 ◇ X4) = ((X0 ◇ X4) ◇ (X3 ◇ X3)) := superpose eq243 eq63 -- backward demodulation 63,243
  have eq251 (X0 X3 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ sK2) ◇ (X3 ◇ X3)) := superpose eq243 eq149 -- backward demodulation 149,243
  have eq445 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X2 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq247 eq14 -- superposition 14,247, 247 into 14, unify on (0).2 in 247 and (0).2 in 14
  have eq766 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq14 eq251 -- superposition 251,14, 14 into 251, unify on (0).2 in 14 and (0).2 in 251
  subsumption eq766 eq445


@[equational_result]
theorem Equation4558_implies_Equation4559 (G : Type*) [Magma G] (h : Equation4558 G) : Equation4559 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 X4 X5 : G) : ((X5 ◇ X4) ◇ X0) = (X4 ◇ ((X3 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 X4 X5 : G) : (X2 ◇ (X4 ◇ X5)) = ((X1 ◇ (X2 ◇ X3)) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ ((X2 ◇ sK2) ◇ X0)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.2 in 19
  have eq127 (X0 X1 X2 X4 X5 : G) : ((X5 ◇ X0) ◇ X2) = ((X4 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq208 (X1 X2 X3 X4 X5 : G) : (X1 ◇ (X3 ◇ X5)) = ((X1 ◇ X2) ◇ (X3 ◇ X4)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq1391 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X1) ◇ X3) = (X0 ◇ (X2 ◇ X5)) := superpose eq127 eq208 -- superposition 208,127, 127 into 208, unify on (0).2 in 127 and (0).2 in 208
  have eq1471 (X0 X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ X2) ◇ ((X0 ◇ sK2) ◇ X3)) := superpose eq208 eq20 -- superposition 20,208, 208 into 20, unify on (0).2 in 208 and (0).2 in 20
  subsumption eq1471 eq1391


@[equational_result]
theorem Equation4558_implies_Equation4568 (G : Type*) [Magma G] (h : Equation4558 G) : Equation4568 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X4)) = ((X5 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X4 ◇ X5)) = (((X3 ◇ X0) ◇ X1) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X1 X2 X3 X4 X5 : G) : (X2 ◇ (X4 ◇ X5)) = ((X1 ◇ (X2 ◇ X3)) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK1 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ ((X2 ◇ sK1) ◇ X0)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.2 in 19
  have eq611 (X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ (X3 ◇ X4)) = (X2 ◇ ((X3 ◇ X5) ◇ X6)) := superpose eq16 eq14 -- superposition 14,16, 16 into 14, unify on (0).2 in 16 and (0).2 in 14
  have eq1031 (X2 X3 X4 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ ((sK1 ◇ X3) ◇ (X2 ◇ X4))) := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).2.2 in 20
  subsumption eq1031 eq611


@[equational_result]
theorem Equation4481_implies_Equation4471 (G : Type*) [Magma G] (h : Equation4481 G) : Equation4471 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq62 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2.1 in 15
  have eq287 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ X0)) = (X3 ◇ (X2 ◇ X2)) := superpose eq15 eq62 -- superposition 62,15, 15 into 62, unify on (0).2 in 15 and (0).1 in 62
  have eq926 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (X0 ◇ X0)) := superpose eq287 eq11 -- superposition 11,287, 287 into 11, unify on (0).2 in 287 and (0).1 in 11
  subsumption eq926 eq287


@[equational_result]
theorem Equation4481_implies_Equation4497 (G : Type*) [Magma G] (h : Equation4481 G) : Equation4497 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq33 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq69 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X5) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  have eq346 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((((sK2 ◇ sK2) ◇ X0) ◇ X1) ◇ X2) := superpose eq68 eq33 -- superposition 33,68, 68 into 33, unify on (0).2 in 68 and (0).2 in 33
  subsumption eq346 eq69


@[equational_result]
theorem Equation4481_implies_Equation4391 (G : Type*) [Magma G] (h : Equation4481 G) : Equation4391 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq33 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK2) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq69 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X5) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  have eq357 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((((sK1 ◇ sK2) ◇ X0) ◇ X1) ◇ X2) := superpose eq68 eq33 -- superposition 33,68, 68 into 33, unify on (0).2 in 68 and (0).2 in 33
  subsumption eq357 eq69


@[equational_result]
theorem Equation4481_implies_Equation4389 (G : Type*) [Magma G] (h : Equation4481 G) : Equation4389 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq37 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq69 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X5) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  have eq354 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((((sK1 ◇ sK1) ◇ X0) ◇ X1) ◇ X2) := superpose eq68 eq37 -- superposition 37,68, 68 into 37, unify on (0).2 in 68 and (0).2 in 37
  subsumption eq354 eq69


@[equational_result]
theorem Equation4481_implies_Equation4355 (G : Type*) [Magma G] (h : Equation4481 G) : Equation4355 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq61 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq286 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ X0)) = (X3 ◇ (X2 ◇ X2)) := superpose eq14 eq61 -- superposition 61,14, 14 into 61, unify on (0).2 in 14 and (0).1 in 61
  have eq799 (X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X2)) = (X3 ◇ (X4 ◇ X4)) := superpose eq286 eq286 -- superposition 286,286, 286 into 286, unify on (0).2 in 286 and (0).1 in 286
  have eq925 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (X0 ◇ X0)) := superpose eq286 eq10 -- superposition 10,286, 286 into 10, unify on (0).2 in 286 and (0).2 in 10
  subsumption eq925 eq799


@[equational_result]
theorem Equation4481_implies_Equation4392 (G : Type*) [Magma G] (h : Equation4481 G) : Equation4392 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq33 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK2) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq69 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X5) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  have eq357 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((((sK1 ◇ sK2) ◇ X0) ◇ X1) ◇ X2) := superpose eq68 eq33 -- superposition 33,68, 68 into 33, unify on (0).2 in 68 and (0).2 in 33
  subsumption eq357 eq69


@[equational_result]
theorem Equation4481_implies_Equation4477 (G : Type*) [Magma G] (h : Equation4481 G) : Equation4477 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq37 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq69 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X5) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  have eq354 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((((sK0 ◇ sK2) ◇ X0) ◇ X1) ◇ X2) := superpose eq68 eq37 -- superposition 37,68, 68 into 37, unify on (0).2 in 68 and (0).2 in 37
  subsumption eq354 eq69


@[equational_result]
theorem Equation4481_implies_Equation4499 (G : Type*) [Magma G] (h : Equation4481 G) : Equation4499 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq37 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq69 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X5) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  have eq354 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((((sK2 ◇ sK2) ◇ X0) ◇ X1) ◇ X2) := superpose eq68 eq37 -- superposition 37,68, 68 into 37, unify on (0).2 in 68 and (0).2 in 37
  subsumption eq354 eq69


@[equational_result]
theorem Equation4481_implies_Equation4384 (G : Type*) [Magma G] (h : Equation4481 G) : Equation4384 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq33 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq69 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X5) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  have eq357 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((((sK0 ◇ sK1) ◇ X0) ◇ X1) ◇ X2) := superpose eq68 eq33 -- superposition 33,68, 68 into 33, unify on (0).2 in 68 and (0).2 in 33
  subsumption eq357 eq69


@[equational_result]
theorem Equation4481_implies_Equation4476 (G : Type*) [Magma G] (h : Equation4481 G) : Equation4476 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq33 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq69 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X5) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  have eq357 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((((sK0 ◇ sK2) ◇ X0) ◇ X1) ◇ X2) := superpose eq68 eq33 -- superposition 33,68, 68 into 33, unify on (0).2 in 68 and (0).2 in 33
  subsumption eq357 eq69


