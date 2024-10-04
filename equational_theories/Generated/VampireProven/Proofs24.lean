import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation3088_implies_Equation3324 (G : Type*) [Magma G] (h : Equation3088 G) : Equation3324 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation3088_implies_Equation3064 (G : Type*) [Magma G] (h : Equation3088 G) : Equation3064 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq21 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq24 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ X0) ◇ sK2) ◇ sK3) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq24 eq21


@[equational_result]
theorem Equation3088_implies_Equation3074 (G : Type*) [Magma G] (h : Equation3088 G) : Equation3074 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq21 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq24 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK1) ◇ X0) ◇ sK2) ◇ sK3) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq24 eq21


@[equational_result]
theorem Equation3092_implies_Equation3063 (G : Type*) [Magma G] (h : Equation3092 G) : Equation3063 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq21 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq24 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ X0) ◇ sK2) ◇ sK2) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq24 eq21


@[equational_result]
theorem Equation1856_implies_Equation158 (G : Type*) [Magma G] (h : Equation1856 G) : Equation158 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq13 (X0 X4 X5 : G) : ((X4 ◇ (X5 ◇ X4)) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.2 in 13
  have eq60 : sK0 ≠ sK0 := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq60 rfl


@[equational_result]
theorem Equation48_implies_Equation614 (G : Type*) [Magma G] (h : Equation48 G) : Equation614 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq13 eq8


@[equational_result]
theorem Equation48_implies_Equation3715 (G : Type*) [Magma G] (h : Equation48 G) : Equation3715 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq14 -- forward demodulation 14,12
  subsumption eq15 rfl


@[equational_result]
theorem Equation48_implies_Equation1629 (G : Type*) [Magma G] (h : Equation48 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11


@[equational_result]
theorem Equation48_implies_Equation1426 (G : Type*) [Magma G] (h : Equation48 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq10 eq9 -- backward demodulation 9,10
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq12 -- backward demodulation 12,11
  subsumption eq14 eq11


@[equational_result]
theorem Equation48_implies_Equation2441 (G : Type*) [Magma G] (h : Equation48 G) : Equation2441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq14 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq15 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq14 -- forward demodulation 14,11
  subsumption eq15 eq11


@[equational_result]
theorem Equation48_implies_Equation2240 (G : Type*) [Magma G] (h : Equation48 G) : Equation2240 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 : sK0 ≠ (sK0 ◇ sK0) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).2 in 11
  subsumption eq15 rfl


@[equational_result]
theorem Equation48_implies_Equation2035 (G : Type*) [Magma G] (h : Equation48 G) : Equation2035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11


@[equational_result]
theorem Equation48_implies_Equation255 (G : Type*) [Magma G] (h : Equation48 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11


@[equational_result]
theorem Equation48_implies_Equation3 (G : Type*) [Magma G] (h : Equation48 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq13 rfl


@[equational_result]
theorem Equation48_implies_Equation3254 (G : Type*) [Magma G] (h : Equation48 G) : Equation3254 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq11 : sK0 ≠ (sK0 ◇ sK0) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).2 in 11
  subsumption eq15 rfl


@[equational_result]
theorem Equation48_implies_Equation2238 (G : Type*) [Magma G] (h : Equation48 G) : Equation2238 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq10 : sK0 ≠ (sK0 ◇ sK0) := superpose eq8 eq9 -- forward demodulation 9,8
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq14 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq14 rfl


@[equational_result]
theorem Equation48_implies_Equation3722 (G : Type*) [Magma G] (h : Equation48 G) : Equation3722 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation48_implies_Equation151 (G : Type*) [Magma G] (h : Equation48 G) : Equation151 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation48_implies_Equation818 (G : Type*) [Magma G] (h : Equation48 G) : Equation818 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq9


@[equational_result]
theorem Equation48_implies_Equation2644 (G : Type*) [Magma G] (h : Equation48 G) : Equation2644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11


@[equational_result]
theorem Equation48_implies_Equation1427 (G : Type*) [Magma G] (h : Equation48 G) : Equation1427 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq9


@[equational_result]
theorem Equation4543_implies_Equation4374 (G : Type*) [Magma G] (h : Equation4543 G) : Equation4374 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq14 (X0 X1 X3 X4 X5 : G) : (X1 ◇ (X4 ◇ X0)) = ((X3 ◇ (X0 ◇ X1)) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq17 (X0 X1 X3 X4 : G) : (X1 ◇ (X3 ◇ X0)) = (X1 ◇ (X4 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq70 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (X0 ◇ sK2)) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  have eq268 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ (X5 ◇ X2)) = ((X1 ◇ (X4 ◇ X0)) ◇ X6) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq302 (X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((X1 ◇ (sK2 ◇ sK3)) ◇ X2) := superpose eq14 eq70 -- superposition 70,14, 14 into 70, unify on (0).2 in 14 and (0).2 in 70
  subsumption eq302 eq268


@[equational_result]
theorem Equation4543_implies_Equation4290 (G : Type*) [Magma G] (h : Equation4543 G) : Equation4290 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq14 (X0 X1 X3 X4 X5 : G) : (X1 ◇ (X4 ◇ X0)) = ((X3 ◇ (X0 ◇ X1)) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq17 (X0 X1 X3 X4 : G) : (X1 ◇ (X3 ◇ X0)) = (X1 ◇ (X4 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq70 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (X0 ◇ sK0)) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  have eq268 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ (X5 ◇ X2)) = ((X1 ◇ (X4 ◇ X0)) ◇ X6) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq302 (X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ (sK0 ◇ sK1)) ◇ X2) := superpose eq14 eq70 -- superposition 70,14, 14 into 70, unify on (0).2 in 14 and (0).2 in 70
  subsumption eq302 eq268


@[equational_result]
theorem Equation4543_implies_Equation4390 (G : Type*) [Magma G] (h : Equation4543 G) : Equation4390 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq14 (X0 X1 X3 X4 X5 : G) : (X1 ◇ (X4 ◇ X0)) = ((X3 ◇ (X0 ◇ X1)) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq195 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ (X5 ◇ X2)) = ((X1 ◇ (X4 ◇ X0)) ◇ X6) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq208 (X1 X2 X3 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((X2 ◇ (X1 ◇ (sK1 ◇ sK1))) ◇ X3) := superpose eq14 eq21 -- superposition 21,14, 14 into 21, unify on (0).2 in 14 and (0).2 in 21
  subsumption eq208 eq195


@[equational_result]
theorem Equation4543_implies_Equation4461 (G : Type*) [Magma G] (h : Equation4543 G) : Equation4461 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq14 (X0 X1 X3 X4 X5 : G) : (X1 ◇ (X4 ◇ X0)) = ((X3 ◇ (X0 ◇ X1)) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (X0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK2) ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq195 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ (X5 ◇ X2)) = ((X1 ◇ (X4 ◇ X0)) ◇ X6) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq208 (X1 X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((X2 ◇ (X1 ◇ (sK2 ◇ sK2))) ◇ X3) := superpose eq14 eq21 -- superposition 21,14, 14 into 21, unify on (0).2 in 14 and (0).2 in 21
  subsumption eq208 eq195


@[equational_result]
theorem Equation4543_implies_Equation4568 (G : Type*) [Magma G] (h : Equation4543 G) : Equation4568 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq14 (X0 X1 X3 X4 X5 : G) : (X1 ◇ (X4 ◇ X0)) = ((X3 ◇ (X0 ◇ X1)) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (X0 ◇ sK3)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK2) ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq195 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ (X5 ◇ X2)) = ((X1 ◇ (X4 ◇ X0)) ◇ X6) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq219 (X1 X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((X2 ◇ (X1 ◇ (sK3 ◇ sK2))) ◇ X3) := superpose eq14 eq21 -- superposition 21,14, 14 into 21, unify on (0).2 in 14 and (0).2 in 21
  subsumption eq219 eq195


@[equational_result]
theorem Equation4543_implies_Equation4490 (G : Type*) [Magma G] (h : Equation4543 G) : Equation4490 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq14 (X0 X1 X3 X4 X5 : G) : (X1 ◇ (X4 ◇ X0)) = ((X3 ◇ (X0 ◇ X1)) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK0) ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq197 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ (X5 ◇ X2)) = ((X1 ◇ (X4 ◇ X0)) ◇ X6) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq221 (X1 X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((X2 ◇ (X1 ◇ (sK2 ◇ sK0))) ◇ X3) := superpose eq14 eq21 -- superposition 21,14, 14 into 21, unify on (0).2 in 14 and (0).2 in 21
  subsumption eq221 eq197


@[equational_result]
theorem Equation4543_implies_Equation4559 (G : Type*) [Magma G] (h : Equation4543 G) : Equation4559 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq14 (X0 X1 X3 X4 X5 : G) : (X1 ◇ (X4 ◇ X0)) = ((X3 ◇ (X0 ◇ X1)) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK3)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK0) ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq197 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ (X5 ◇ X2)) = ((X1 ◇ (X4 ◇ X0)) ◇ X6) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq221 (X1 X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((X2 ◇ (X1 ◇ (sK3 ◇ sK0))) ◇ X3) := superpose eq14 eq21 -- superposition 21,14, 14 into 21, unify on (0).2 in 14 and (0).2 in 21
  subsumption eq221 eq197


@[equational_result]
theorem Equation451_implies_Equation4518 (G : Type*) [Magma G] (h : Equation451 G) : Equation4518 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK3) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ ((sK0 ◇ sK3) ◇ sK0) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq17 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.2 in 15
  have eq21 : sK0 ≠ (sK0 ◇ sK0) := superpose eq17 eq16 -- backward demodulation 16,17
  subsumption eq21 eq17


@[equational_result]
theorem Equation451_implies_Equation3917 (G : Type*) [Magma G] (h : Equation451 G) : Equation3917 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq17 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.2 in 15
  have eq21 : sK0 ≠ (sK0 ◇ sK1) := superpose eq17 eq16 -- backward demodulation 16,17
  subsumption eq21 eq17


@[equational_result]
theorem Equation451_implies_Equation1045 (G : Type*) [Magma G] (h : Equation451 G) : Equation1045 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq16 eq15


@[equational_result]
theorem Equation451_implies_Equation4510 (G : Type*) [Magma G] (h : Equation451 G) : Equation4510 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq17 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.2 in 15
  have eq21 : sK0 ≠ (sK0 ◇ sK0) := superpose eq17 eq16 -- backward demodulation 16,17
  subsumption eq21 eq17


@[equational_result]
theorem Equation451_implies_Equation3935 (G : Type*) [Magma G] (h : Equation451 G) : Equation3935 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq16 rfl


@[equational_result]
theorem Equation451_implies_Equation460 (G : Type*) [Magma G] (h : Equation451 G) : Equation460 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq17 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.2 in 15
  have eq21 : sK0 ≠ sK0 := superpose eq17 eq16 -- superposition 16,17, 17 into 16, unify on (0).2 in 17 and (0).2 in 16
  subsumption eq21 rfl


@[equational_result]
theorem Equation451_implies_Equation646 (G : Type*) [Magma G] (h : Equation451 G) : Equation646 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X3)) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X3)) = X2 := superpose eq12 eq13 -- backward demodulation 13,12
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq17 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.2 in 15
  have eq21 : sK0 ≠ sK0 := superpose eq17 eq16 -- superposition 16,17, 17 into 16, unify on (0).2 in 17 and (0).2 in 16
  subsumption eq21 rfl


@[equational_result]
theorem Equation451_implies_Equation1836 (G : Type*) [Magma G] (h : Equation451 G) : Equation1836 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq16 eq15


@[equational_result]
theorem Equation451_implies_Equation3932 (G : Type*) [Magma G] (h : Equation451 G) : Equation3932 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK2) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq17 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.2 in 15
  have eq21 : sK0 ≠ (sK0 ◇ sK1) := superpose eq17 eq16 -- backward demodulation 16,17
  subsumption eq21 eq17


@[equational_result]
theorem Equation451_implies_Equation4402 (G : Type*) [Magma G] (h : Equation451 G) : Equation4402 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK1) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq17 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.2 in 15
  have eq21 : sK0 ≠ (sK0 ◇ sK1) := superpose eq17 eq16 -- backward demodulation 16,17
  subsumption eq21 eq17


@[equational_result]
theorem Equation451_implies_Equation4478 (G : Type*) [Magma G] (h : Equation451 G) : Equation4478 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK3) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.2 in 15
  have eq21 : sK0 ≠ (sK0 ◇ sK3) := superpose eq17 eq16 -- backward demodulation 16,17
  subsumption eq21 eq17


@[equational_result]
theorem Equation451_implies_Equation1237 (G : Type*) [Magma G] (h : Equation451 G) : Equation1237 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq17 : sK0 ≠ sK0 := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation451_implies_Equation3672 (G : Type*) [Magma G] (h : Equation451 G) : Equation3672 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.2 in 15
  have eq21 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq16 eq10 -- backward demodulation 10,16
  have eq22 : sK0 ≠ (sK0 ◇ sK0) := superpose eq16 eq21 -- forward demodulation 21,16
  subsumption eq22 eq16


@[equational_result]
theorem Equation451_implies_Equation4469 (G : Type*) [Magma G] (h : Equation451 G) : Equation4469 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.2 in 15
  have eq21 : sK0 ≠ (sK0 ◇ sK0) := superpose eq17 eq16 -- backward demodulation 16,17
  subsumption eq21 eq17


@[equational_result]
theorem Equation451_implies_Equation4396 (G : Type*) [Magma G] (h : Equation451 G) : Equation4396 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq17 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.2 in 15
  have eq21 : sK0 ≠ (sK0 ◇ sK1) := superpose eq17 eq16 -- backward demodulation 16,17
  subsumption eq21 eq17


@[equational_result]
theorem Equation2486_implies_Equation2490 (G : Type*) [Magma G] (h : Equation2486 G) : Equation2490 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK3)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ (X0 ◇ X2)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq13 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq21 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq21 eq13


@[equational_result]
theorem Equation2275_implies_Equation1457 (G : Type*) [Magma G] (h : Equation2275 G) : Equation1457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2275_implies_Equation2482 (G : Type*) [Magma G] (h : Equation2275 G) : Equation2482 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation2275_implies_Equation1858 (G : Type*) [Magma G] (h : Equation2275 G) : Equation1858 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2275_implies_Equation1430 (G : Type*) [Magma G] (h : Equation2275 G) : Equation1430 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2275_implies_Equation159 (G : Type*) [Magma G] (h : Equation2275 G) : Equation159 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2275_implies_Equation3088 (G : Type*) [Magma G] (h : Equation2275 G) : Equation3088 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK0) ◇ sK3) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK3) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation2275_implies_Equation1437 (G : Type*) [Magma G] (h : Equation2275 G) : Equation1437 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation2275_implies_Equation1450 (G : Type*) [Magma G] (h : Equation2275 G) : Equation1450 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2602_implies_Equation3878 (G : Type*) [Magma G] (h : Equation2602 G) : Equation3878 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (((X3 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq31 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq26 -- forward demodulation 26,9
  have eq34 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq31 eq10 -- backward demodulation 10,31
  have eq38 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X2 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq11 eq31 -- superposition 31,11, 11 into 31, unify on (0).2 in 11 and (0).1 in 31
  have eq49 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ X0) := superpose eq31 eq38 -- forward demodulation 38,31
  have eq111 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq49 eq34 -- superposition 34,49, 49 into 34, unify on (0).2 in 49 and (0).2 in 34
  subsumption eq111 eq49


@[equational_result]
theorem Equation2602_implies_Equation870 (G : Type*) [Magma G] (h : Equation2602 G) : Equation870 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X2 ◇ X2) ◇ X3))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq19 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1 in 11
  have eq44 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X2 ◇ ((X3 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq57 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ X0) := superpose eq9 eq44 -- forward demodulation 44,9
  have eq109 (X0 : G) : sK0 ≠ (sK1 ◇ ((X0 ◇ X0) ◇ (sK0 ◇ sK1))) := superpose eq57 eq10 -- superposition 10,57, 57 into 10, unify on (0).2 in 57 and (0).2.2.1 in 10
  have eq440 (X1 : G) : sK0 ≠ (sK1 ◇ ((X1 ◇ (sK0 ◇ sK1)) ◇ X1)) := superpose eq11 eq109 -- superposition 109,11, 11 into 109, unify on (0).2 in 11 and (0).2.2 in 109
  have eq1502 (X0 X1 : G) : sK0 ≠ (sK1 ◇ (((X1 ◇ X1) ◇ sK0) ◇ ((X0 ◇ X0) ◇ sK1))) := superpose eq19 eq440 -- superposition 440,19, 19 into 440, unify on (0).2 in 19 and (0).2.2.1 in 440
  subsumption eq1502 eq12


@[equational_result]
theorem Equation2602_implies_Equation1049 (G : Type*) [Magma G] (h : Equation2602 G) : Equation1049 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (((X3 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq31 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq26 -- forward demodulation 26,9
  have eq34 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq31 eq10 -- backward demodulation 10,31
  subsumption eq34 eq31


@[equational_result]
theorem Equation2602_implies_Equation3721 (G : Type*) [Magma G] (h : Equation2602 G) : Equation3721 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (((X3 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq30 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq26 -- forward demodulation 26,9
  have eq69 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq30 eq10 -- superposition 10,30, 30 into 10, unify on (0).2 in 30 and (0).2 in 10
  subsumption eq69 rfl


@[equational_result]
theorem Equation2602_implies_Equation411 (G : Type*) [Magma G] (h : Equation2602 G) : Equation411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X1) ◇ X2) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq25 (X0 X1 X2 X3 : G) : (((X3 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1 in 8
  have eq29 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq8 eq25 -- forward demodulation 25,8
  have eq32 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq29 eq9 -- backward demodulation 9,29
  subsumption eq32 eq29


@[equational_result]
theorem Equation2602_implies_Equation3928 (G : Type*) [Magma G] (h : Equation2602 G) : Equation3928 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (((X3 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq30 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq26 -- forward demodulation 26,9
  have eq33 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq30 eq10 -- backward demodulation 10,30
  subsumption eq33 rfl


@[equational_result]
theorem Equation2602_implies_Equation1729 (G : Type*) [Magma G] (h : Equation2602 G) : Equation1729 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq20 (X1 X2 X3 : G) : ((X3 ◇ X3) ◇ ((X1 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq27 (X0 : G) : sK0 ≠ ((sK1 ◇ sK1) ◇ ((X0 ◇ X0) ◇ sK0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2.2 in 10
  subsumption eq27 eq20


@[equational_result]
theorem Equation2602_implies_Equation3323 (G : Type*) [Magma G] (h : Equation2602 G) : Equation3323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (((X3 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq30 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq26 -- forward demodulation 26,9
  have eq33 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq30 eq10 -- backward demodulation 10,30
  subsumption eq33 rfl


@[equational_result]
theorem Equation2602_implies_Equation444 (G : Type*) [Magma G] (h : Equation2602 G) : Equation444 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (((X3 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq30 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq26 -- forward demodulation 26,9
  have eq33 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq30 eq10 -- backward demodulation 10,30
  subsumption eq33 eq30


@[equational_result]
theorem Equation2602_implies_Equation40 (G : Type*) [Magma G] (h : Equation2602 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X2 ◇ X2) ◇ X3))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq44 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X2 ◇ ((X3 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq57 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ X0) := superpose eq9 eq44 -- forward demodulation 44,9
  have eq96 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq57 eq10 -- superposition 10,57, 57 into 10, unify on (0).2 in 57 and (0).2 in 10
  subsumption eq96 eq57


@[equational_result]
theorem Equation2602_implies_Equation3278 (G : Type*) [Magma G] (h : Equation2602 G) : Equation3278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (((X3 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq30 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq26 -- forward demodulation 26,9
  have eq33 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq30 eq10 -- backward demodulation 10,30
  have eq37 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X2 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq11 eq30 -- superposition 30,11, 11 into 30, unify on (0).2 in 11 and (0).1 in 30
  have eq48 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ X0) := superpose eq30 eq37 -- forward demodulation 37,30
  have eq110 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq48 eq33 -- superposition 33,48, 48 into 33, unify on (0).2 in 48 and (0).2 in 33
  subsumption eq110 eq48


@[equational_result]
theorem Equation2602_implies_Equation1635 (G : Type*) [Magma G] (h : Equation2602 G) : Equation1635 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq20 (X1 X2 X3 : G) : ((X3 ◇ X3) ◇ ((X1 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq30 (X0 : G) : sK0 ≠ ((sK0 ◇ sK0) ◇ ((X0 ◇ X0) ◇ sK0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2.2 in 10
  subsumption eq30 eq20


@[equational_result]
theorem Equation2602_implies_Equation4341 (G : Type*) [Magma G] (h : Equation2602 G) : Equation4341 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (((X3 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq30 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq26 -- forward demodulation 26,9
  have eq33 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq30 eq10 -- backward demodulation 10,30
  subsumption eq33 eq30


@[equational_result]
theorem Equation2602_implies_Equation3253 (G : Type*) [Magma G] (h : Equation2602 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X1) ◇ X2) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq25 (X0 X1 X2 X3 : G) : (((X3 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1 in 8
  have eq29 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq8 eq25 -- forward demodulation 25,8
  have eq32 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq29 eq9 -- backward demodulation 9,29
  subsumption eq32 rfl


@[equational_result]
theorem Equation2602_implies_Equation414 (G : Type*) [Magma G] (h : Equation2602 G) : Equation414 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (((X3 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq30 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq26 -- forward demodulation 26,9
  have eq33 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq30 eq10 -- backward demodulation 10,30
  subsumption eq33 eq30


@[equational_result]
theorem Equation2602_implies_Equation917 (G : Type*) [Magma G] (h : Equation2602 G) : Equation917 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X2 ◇ X2) ◇ X3))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq19 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1 in 11
  have eq44 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X2 ◇ ((X3 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq57 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ X0) := superpose eq9 eq44 -- forward demodulation 44,9
  have eq109 (X0 : G) : sK0 ≠ (sK1 ◇ ((X0 ◇ X0) ◇ (sK0 ◇ sK1))) := superpose eq57 eq10 -- superposition 10,57, 57 into 10, unify on (0).2 in 57 and (0).2.2.1 in 10
  have eq440 (X1 : G) : sK0 ≠ (sK1 ◇ ((X1 ◇ (sK0 ◇ sK1)) ◇ X1)) := superpose eq11 eq109 -- superposition 109,11, 11 into 109, unify on (0).2 in 11 and (0).2.2 in 109
  have eq1502 (X0 X1 : G) : sK0 ≠ (sK1 ◇ (((X1 ◇ X1) ◇ sK0) ◇ ((X0 ◇ X0) ◇ sK1))) := superpose eq19 eq440 -- superposition 440,19, 19 into 440, unify on (0).2 in 19 and (0).2.2.1 in 440
  subsumption eq1502 eq12


@[equational_result]
theorem Equation2602_implies_Equation1740 (G : Type*) [Magma G] (h : Equation2602 G) : Equation1740 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq20 (X1 X2 X3 : G) : ((X3 ◇ X3) ◇ ((X1 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq29 (X0 : G) : sK0 ≠ ((sK1 ◇ sK1) ◇ ((X0 ◇ X0) ◇ sK0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2.2 in 10
  subsumption eq29 eq20


@[equational_result]
theorem Equation2602_implies_Equation3677 (G : Type*) [Magma G] (h : Equation2602 G) : Equation3677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X2 ◇ X2) ◇ X3))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq44 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X2 ◇ ((X3 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq57 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ X0) := superpose eq9 eq44 -- forward demodulation 44,9
  have eq96 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq57 eq10 -- superposition 10,57, 57 into 10, unify on (0).2 in 57 and (0).2 in 10
  subsumption eq96 eq57


@[equational_result]
theorem Equation2602_implies_Equation820 (G : Type*) [Magma G] (h : Equation2602 G) : Equation820 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (((X3 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq30 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq26 -- forward demodulation 26,9
  have eq33 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq30 eq10 -- backward demodulation 10,30
  subsumption eq33 eq30


@[equational_result]
theorem Equation588_implies_Equation4175 (G : Type*) [Magma G] (h : Equation588 G) : Equation4175 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1 in 13
  have eq25 (X0 : G) : (sK0 ◇ sK1) ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  subsumption eq25 eq16


@[equational_result]
theorem Equation588_implies_Equation495 (G : Type*) [Magma G] (h : Equation588 G) : Equation495 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := mod_symm nh
  have eq13 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq9


@[equational_result]
theorem Equation588_implies_Equation4209 (G : Type*) [Magma G] (h : Equation588 G) : Equation4209 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1 in 13
  have eq25 (X0 : G) : (sK0 ◇ sK1) ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  subsumption eq25 eq16


@[equational_result]
theorem Equation938_implies_Equation791 (G : Type*) [Magma G] (h : Equation938 G) : Equation791 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK3 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X0 ◇ (X3 ◇ (X4 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X3 X4 : G) : (X3 ◇ X4) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ ((X0 ◇ sK0) ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.2.1 in 10
  subsumption eq20 eq11


@[equational_result]
theorem Equation2575_implies_Equation769 (G : Type*) [Magma G] (h : Equation2575 G) : Equation769 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK1 ◇ sK3) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1)))) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq13 (X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X2) = X2 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq52 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq14 eq13 -- superposition 13,14, 14 into 13, unify on (0).2 in 14 and (0).1.1 in 13
  have eq62 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X2) = X2 := superpose eq52 eq11 -- backward demodulation 11,52
  have eq75 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = ((X2 ◇ (X3 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq9 eq62 -- superposition 62,9, 9 into 62, unify on (0).2 in 9 and (0).1.1.2.2 in 62
  have eq258 (X0 X1 X2 : G) : (X2 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) := superpose eq75 eq13 -- superposition 13,75, 75 into 13, unify on (0).2 in 75 and (0).1.1 in 13
  have eq394 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq258 eq13 -- superposition 13,258, 258 into 13, unify on (0).2 in 258 and (0).1.1 in 13
  have eq438 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq394 eq9 -- backward demodulation 9,394
  have eq440 (X2 X3 : G) : (X2 ◇ X3) = X3 := superpose eq394 eq13 -- backward demodulation 13,394
  have eq481 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq438 eq10 -- backward demodulation 10,438
  have eq487 : sK0 ≠ (sK1 ◇ sK0) := superpose eq440 eq481 -- backward demodulation 481,440
  subsumption eq487 eq440


@[equational_result]
theorem Equation2575_implies_Equation2525 (G : Type*) [Magma G] (h : Equation2575 G) : Equation2525 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK2) ◇ sK3)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1)))) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq13 (X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X2) = X2 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq52 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq14 eq13 -- superposition 13,14, 14 into 13, unify on (0).2 in 14 and (0).1.1 in 13
  have eq62 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X2) = X2 := superpose eq52 eq11 -- backward demodulation 11,52
  have eq75 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = ((X2 ◇ (X3 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq9 eq62 -- superposition 62,9, 9 into 62, unify on (0).2 in 9 and (0).1.1.2.2 in 62
  have eq258 (X0 X1 X2 : G) : (X2 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) := superpose eq75 eq13 -- superposition 13,75, 75 into 13, unify on (0).2 in 75 and (0).1.1 in 13
  have eq394 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq258 eq13 -- superposition 13,258, 258 into 13, unify on (0).2 in 258 and (0).1.1 in 13
  have eq438 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq394 eq9 -- backward demodulation 9,394
  have eq481 : sK0 ≠ ((sK1 ◇ sK3) ◇ sK0) := superpose eq438 eq10 -- backward demodulation 10,438
  subsumption eq481 eq438


@[equational_result]
theorem Equation1047_implies_Equation459 (G : Type*) [Magma G] (h : Equation1047 G) : Equation459 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1)))) := mod_symm nh
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
theorem Equation1047_implies_Equation4382 (G : Type*) [Magma G] (h : Equation1047 G) : Equation4382 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq17 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq35 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.2.2 in 12
  have eq39 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq17 eq35 -- forward demodulation 35,17
  have eq40 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq39 eq10 -- backward demodulation 10,39
  have eq43 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.2 in 12
  have eq55 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq43 eq17 -- backward demodulation 17,43
  have eq66 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq55 eq12 -- backward demodulation 12,55
  have eq72 : sK0 ≠ (sK0 ◇ sK0) := superpose eq66 eq40 -- backward demodulation 40,66
  subsumption eq72 eq43


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
theorem Equation516_implies_Equation4134 (G : Type*) [Magma G] (h : Equation516 G) : Equation4134 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 : G) : (X0 ◇ sK1) ≠ (((X0 ◇ sK1) ◇ sK2) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).1 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation516_implies_Equation520 (G : Type*) [Magma G] (h : Equation516 G) : Equation520 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq9


@[equational_result]
theorem Equation516_implies_Equation603 (G : Type*) [Magma G] (h : Equation516 G) : Equation603 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq30 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (X0 ◇ sK0)))) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).2.2.2.2 in 15
  subsumption eq30 eq16


@[equational_result]
theorem Equation2279_implies_Equation4073 (G : Type*) [Magma G] (h : Equation2279 G) : Equation4073 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq23 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq27 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq23 eq10 -- backward demodulation 10,23
  subsumption eq27 rfl


@[equational_result]
theorem Equation2279_implies_Equation1434 (G : Type*) [Magma G] (h : Equation2279 G) : Equation1434 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X1))) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ (X2 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X4)))) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq19 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ (X3 ◇ X0)) = X2 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq23 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq30 (X0 X2 X3 : G) : (X2 ◇ X0) = (X2 ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2.1 in 12
  have eq51 (X0 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ (X2 ◇ (X4 ◇ ((X0 ◇ X2) ◇ X4)))) = X3 := superpose eq30 eq13 -- backward demodulation 13,30
  have eq58 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2))) = X3 := superpose eq30 eq51 -- forward demodulation 51,30
  have eq90 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq23 eq19 -- superposition 19,23, 23 into 19, unify on (0).2 in 23 and (0).1.1 in 19
  have eq94 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))) := superpose eq90 eq10 -- backward demodulation 10,90
  subsumption eq94 eq58


@[equational_result]
theorem Equation2279_implies_Equation3083 (G : Type*) [Magma G] (h : Equation2279 G) : Equation3083 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq23 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq27 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK2) := superpose eq23 eq10 -- backward demodulation 10,23
  subsumption eq27 eq23


@[equational_result]
theorem Equation2279_implies_Equation1442 (G : Type*) [Magma G] (h : Equation2279 G) : Equation1442 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq22 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ X2) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq23 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq100 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).2 in 10
  subsumption eq100 eq23


@[equational_result]
theorem Equation2279_implies_Equation3459 (G : Type*) [Magma G] (h : Equation2279 G) : Equation3459 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq23 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq27 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq23 eq10 -- backward demodulation 10,23
  subsumption eq27 rfl


@[equational_result]
theorem Equation2279_implies_Equation1861 (G : Type*) [Magma G] (h : Equation2279 G) : Equation1861 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq23 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq88 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq88 rfl


@[equational_result]
theorem Equation2279_implies_Equation3308 (G : Type*) [Magma G] (h : Equation2279 G) : Equation3308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq19 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ (X3 ◇ X0)) = X2 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq22 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ X2) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq23 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq90 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq23 eq19 -- superposition 19,23, 23 into 19, unify on (0).2 in 23 and (0).1.1 in 19
  have eq94 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := superpose eq90 eq10 -- backward demodulation 10,90
  subsumption eq94 eq22


@[equational_result]
theorem Equation2279_implies_Equation2485 (G : Type*) [Magma G] (h : Equation2279 G) : Equation2485 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq23 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq27 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq23 eq10 -- backward demodulation 10,23
  subsumption eq27 eq23


@[equational_result]
theorem Equation2279_implies_Equation2263 (G : Type*) [Magma G] (h : Equation2279 G) : Equation2263 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq22 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ X2) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq23 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq27 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq22 eq10 -- backward demodulation 10,22
  have eq30 : sK0 ≠ sK0 := superpose eq23 eq27 -- superposition 27,23, 23 into 27, unify on (0).2 in 23 and (0).2 in 27
  subsumption eq30 rfl


@[equational_result]
theorem Equation2279_implies_Equation3511 (G : Type*) [Magma G] (h : Equation2279 G) : Equation3511 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X1))) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq30 (X0 X2 X3 : G) : (X2 ◇ X0) = (X2 ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2.1 in 12
  have eq33 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = (X3 ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2 in 12
  have eq62 (X0 X1 X3 : G) : (X3 ◇ X1) = (X3 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq30 eq33 -- forward demodulation 33,30
  have eq181 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq62 eq10 -- superposition 10,62, 62 into 10, unify on (0).2 in 62 and (0).2 in 10
  subsumption eq181 rfl


@[equational_result]
theorem Equation2279_implies_Equation4127 (G : Type*) [Magma G] (h : Equation2279 G) : Equation4127 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq23 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq88 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq88 rfl


@[equational_result]
theorem Equation2279_implies_Equation3534 (G : Type*) [Magma G] (h : Equation2279 G) : Equation3534 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X1))) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq30 (X0 X2 X3 : G) : (X2 ◇ X0) = (X2 ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2.1 in 12
  have eq33 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = (X3 ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2 in 12
  have eq62 (X0 X1 X3 : G) : (X3 ◇ X1) = (X3 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq30 eq33 -- forward demodulation 33,30
  have eq193 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq62 eq10 -- superposition 10,62, 62 into 10, unify on (0).2 in 62 and (0).2 in 10
  subsumption eq193 rfl


@[equational_result]
theorem Equation2279_implies_Equation4135 (G : Type*) [Magma G] (h : Equation2279 G) : Equation4135 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq23 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq88 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq88 rfl


@[equational_result]
theorem Equation2279_implies_Equation1876 (G : Type*) [Magma G] (h : Equation2279 G) : Equation1876 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq19 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ (X3 ◇ X0)) = X2 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq93 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq93 rfl


@[equational_result]
theorem Equation2279_implies_Equation1838 (G : Type*) [Magma G] (h : Equation2279 G) : Equation1838 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq23 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq88 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq88 rfl


@[equational_result]
theorem Equation2279_implies_Equation1873 (G : Type*) [Magma G] (h : Equation2279 G) : Equation1873 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq23 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq88 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq88 rfl


@[equational_result]
theorem Equation549_implies_Equation491 (G : Type*) [Magma G] (h : Equation549 G) : Equation491 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq13 (X1 X2 X3 : G) : (X3 ◇ X2) = (X1 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq21 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq24 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  subsumption eq24 eq21


@[equational_result]
theorem Equation549_implies_Equation479 (G : Type*) [Magma G] (h : Equation549 G) : Equation479 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq13 (X1 X2 X3 : G) : (X3 ◇ X2) = (X1 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq21 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq24 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  subsumption eq24 eq21


@[equational_result]
theorem Equation2491_implies_Equation3068 (G : Type*) [Magma G] (h : Equation2491 G) : Equation3068 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X3 X4 : G) : ((X4 ◇ X0) ◇ X3) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation2491_implies_Equation4073 (G : Type*) [Magma G] (h : Equation2491 G) : Equation4073 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X3 X4 : G) : ((X4 ◇ X0) ◇ X3) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 rfl


@[equational_result]
theorem Equation2491_implies_Equation2249 (G : Type*) [Magma G] (h : Equation2491 G) : Equation2249 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq12 (X0 X3 X4 : G) : ((X4 ◇ X0) ◇ X3) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation2491_implies_Equation4284 (G : Type*) [Magma G] (h : Equation2491 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X3 X4 : G) : ((X4 ◇ X0) ◇ X3) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ X5) = (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X5))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X5 : G) : (X0 ◇ X1) = (X0 ◇ X5) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq25 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ X0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq25 eq15


@[equational_result]
theorem Equation2491_implies_Equation2452 (G : Type*) [Magma G] (h : Equation2491 G) : Equation2452 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X3 X4 : G) : ((X4 ◇ X0) ◇ X3) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation2491_implies_Equation4283 (G : Type*) [Magma G] (h : Equation2491 G) : Equation4283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X3 X4 : G) : ((X4 ◇ X0) ◇ X3) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ X5) = (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X5))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X5 : G) : (X0 ◇ X1) = (X0 ◇ X5) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq25 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ X0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq25 eq15


@[equational_result]
theorem Equation2491_implies_Equation1657 (G : Type*) [Magma G] (h : Equation2491 G) : Equation1657 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X3 X4 : G) : ((X4 ◇ X0) ◇ X3) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation2491_implies_Equation3526 (G : Type*) [Magma G] (h : Equation2491 G) : Equation3526 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X3 X4 : G) : ((X4 ◇ X0) ◇ X3) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 rfl


@[equational_result]
theorem Equation2491_implies_Equation3084 (G : Type*) [Magma G] (h : Equation2491 G) : Equation3084 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq12 (X0 X3 X4 : G) : ((X4 ◇ X0) ◇ X3) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK3) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation2889_implies_Equation4597 (G : Type*) [Magma G] (h : Equation2889 G) : Equation4597 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = ((X0 ◇ X3) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X4 X5 : G) : (X4 ◇ X0) = (X4 ◇ X5) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq45 (X0 X3 X4 X5 X6 : G) : ((X0 ◇ X3) ◇ X4) = ((X0 ◇ X5) ◇ X6) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq98 (X0 : G) : ((sK0 ◇ X0) ◇ sK1) ≠ ((sK0 ◇ X0) ◇ sK2) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).1.1 in 10
  subsumption eq98 eq45


@[equational_result]
theorem Equation2889_implies_Equation2663 (G : Type*) [Magma G] (h : Equation2889 G) : Equation2663 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = ((X0 ◇ X3) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq28 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ X4) ◇ (X1 ◇ X2)) ◇ X5) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq70 (X0 X1 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq70 eq28


@[equational_result]
theorem Equation2889_implies_Equation2052 (G : Type*) [Magma G] (h : Equation2889 G) : Equation2052 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = ((X0 ◇ X3) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X4 X5 : G) : (X4 ◇ X0) = (X4 ◇ X5) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq33 (X0 X1 X3 X4 X5 X6 : G) : (((X0 ◇ ((X3 ◇ X4) ◇ X5)) ◇ X1) ◇ X6) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq40 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X6) ◇ X7) = (((X0 ◇ X4) ◇ X5) ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq76 (X0 X1 X4 X5 : G) : (((X0 ◇ X4) ◇ X5) ◇ X1) = X0 := superpose eq33 eq40 -- forward demodulation 40,33
  have eq98 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK0) ◇ (sK0 ◇ sK2)) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2.1.1 in 10
  subsumption eq98 eq76


@[equational_result]
theorem Equation2889_implies_Equation261 (G : Type*) [Magma G] (h : Equation2889 G) : Equation261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = ((X0 ◇ X3) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X4 X5 : G) : (X4 ◇ X0) = (X4 ◇ X5) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq33 (X0 X1 X3 X4 X5 X6 : G) : (((X0 ◇ ((X3 ◇ X4) ◇ X5)) ◇ X1) ◇ X6) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq40 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X6) ◇ X7) = (((X0 ◇ X4) ◇ X5) ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq76 (X0 X1 X4 X5 : G) : (((X0 ◇ X4) ◇ X5) ◇ X1) = X0 := superpose eq33 eq40 -- forward demodulation 40,33
  have eq98 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK0) ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2.1.1 in 10
  subsumption eq98 eq76


@[equational_result]
theorem Equation2889_implies_Equation2047 (G : Type*) [Magma G] (h : Equation2889 G) : Equation2047 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = ((X0 ◇ X3) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X4 X5 : G) : (X4 ◇ X0) = (X4 ◇ X5) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq31 (X0 X1 X3 X4 X5 X6 : G) : (((X0 ◇ ((X3 ◇ X4) ◇ X5)) ◇ X1) ◇ X6) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq40 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X6) ◇ X7) = (((X0 ◇ X4) ◇ X5) ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq76 (X0 X1 X4 X5 : G) : (((X0 ◇ X4) ◇ X5) ◇ X1) = X0 := superpose eq31 eq40 -- forward demodulation 40,31
  have eq111 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ X0) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq111 eq76


@[equational_result]
theorem Equation2889_implies_Equation3523 (G : Type*) [Magma G] (h : Equation2889 G) : Equation3523 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq13 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X4 X5 : G) : (X4 ◇ X0) = (X4 ◇ X5) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq30 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq30 eq17


@[equational_result]
theorem Equation2889_implies_Equation2691 (G : Type*) [Magma G] (h : Equation2889 G) : Equation2691 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK3)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = ((X0 ◇ X3) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq26 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ X4) ◇ (X1 ◇ X2)) ◇ X5) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq70 (X0 X1 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq70 eq26


@[equational_result]
theorem Equation2851_implies_Equation267 (G : Type*) [Magma G] (h : Equation2851 G) : Equation267 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq13 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1 in 13
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq86 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK2) ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2.1.1 in 10
  subsumption eq86 eq21


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
theorem Equation2286_implies_Equation3526 (G : Type*) [Magma G] (h : Equation2286 G) : Equation3526 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ (X5 ◇ X0)) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq98 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq98 rfl


@[equational_result]
theorem Equation2286_implies_Equation205 (G : Type*) [Magma G] (h : Equation2286 G) : Equation205 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ (X5 ◇ X0)) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2286_implies_Equation3521 (G : Type*) [Magma G] (h : Equation2286 G) : Equation3521 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ (X5 ◇ X0)) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq116 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq116 rfl


@[equational_result]
theorem Equation2286_implies_Equation1430 (G : Type*) [Magma G] (h : Equation2286 G) : Equation1430 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ (X5 ◇ X0)) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4)))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq21 (X0 X1 X5 : G) : ((X5 ◇ X0) ◇ (X0 ◇ X1)) = X5 := superpose eq16 eq12 -- backward demodulation 12,16
  have eq28 : sK0 ≠ sK0 := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq28 rfl


@[equational_result]
theorem Equation2286_implies_Equation160 (G : Type*) [Magma G] (h : Equation2286 G) : Equation160 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ (X5 ◇ X0)) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4)))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq21 (X0 X1 X5 : G) : ((X5 ◇ X0) ◇ (X0 ◇ X1)) = X5 := superpose eq16 eq12 -- backward demodulation 12,16
  have eq28 : sK0 ≠ sK0 := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq28 rfl


@[equational_result]
theorem Equation2286_implies_Equation151 (G : Type*) [Magma G] (h : Equation2286 G) : Equation151 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X4 X5 : G) : ((X4 ◇ (X5 ◇ X0)) ◇ X5) = X4 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4)))) = X5 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq15 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq20 (X0 X1 X5 : G) : ((X5 ◇ X0) ◇ (X0 ◇ X1)) = X5 := superpose eq15 eq11 -- backward demodulation 11,15
  have eq27 : sK0 ≠ sK0 := superpose eq20 eq9 -- superposition 9,20, 20 into 9, unify on (0).2 in 20 and (0).2 in 9
  subsumption eq27 rfl


@[equational_result]
theorem Equation2286_implies_Equation4357 (G : Type*) [Magma G] (h : Equation2286 G) : Equation4357 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ (X5 ◇ X0)) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4)))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq21 (X0 X1 X5 : G) : ((X5 ◇ X0) ◇ (X0 ◇ X1)) = X5 := superpose eq16 eq12 -- backward demodulation 12,16
  have eq23 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).1.1 in 21
  have eq174 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq174 eq23


@[equational_result]
theorem Equation2286_implies_Equation3525 (G : Type*) [Magma G] (h : Equation2286 G) : Equation3525 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ (X5 ◇ X0)) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq116 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq116 rfl


@[equational_result]
theorem Equation2286_implies_Equation3523 (G : Type*) [Magma G] (h : Equation2286 G) : Equation3523 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ (X5 ◇ X0)) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq116 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq116 rfl


@[equational_result]
theorem Equation2286_implies_Equation1453 (G : Type*) [Magma G] (h : Equation2286 G) : Equation1453 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ (X5 ◇ X0)) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4)))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq21 (X0 X1 X5 : G) : ((X5 ◇ X0) ◇ (X0 ◇ X1)) = X5 := superpose eq16 eq12 -- backward demodulation 12,16
  have eq28 : sK0 ≠ sK0 := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq28 rfl


@[equational_result]
theorem Equation2286_implies_Equation209 (G : Type*) [Magma G] (h : Equation2286 G) : Equation209 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ (X5 ◇ X0)) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation532_implies_Equation395 (G : Type*) [Magma G] (h : Equation532 G) : Equation395 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation532_implies_Equation3877 (G : Type*) [Magma G] (h : Equation532 G) : Equation3877 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation3054_implies_Equation4672 (G : Type*) [Magma G] (h : Equation3054 G) : Equation4672 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK1) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation3054_implies_Equation3319 (G : Type*) [Magma G] (h : Equation3054 G) : Equation3319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq26 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1.1 in 9
  have eq30 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq26 -- forward demodulation 26,9
  have eq79 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ X0) := superpose eq30 eq10 -- superposition 10,30, 30 into 10, unify on (0).2 in 30 and (0).2 in 10
  subsumption eq79 eq30


@[equational_result]
theorem Equation3054_implies_Equation3469 (G : Type*) [Magma G] (h : Equation3054 G) : Equation3469 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq26 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1.1 in 9
  have eq32 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq26 -- forward demodulation 26,9
  have eq51 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq32 eq14 -- superposition 14,32, 32 into 14, unify on (0).2 in 32 and (0).2 in 14
  subsumption eq51 eq32


@[equational_result]
theorem Equation3054_implies_Equation3458 (G : Type*) [Magma G] (h : Equation3054 G) : Equation3458 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq28 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1.1 in 9
  have eq32 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq28 -- forward demodulation 28,9
  have eq52 (X0 : G) : (sK0 ◇ X0) ≠ (sK0 ◇ ((sK0 ◇ X0) ◇ sK0)) := superpose eq32 eq14 -- superposition 14,32, 32 into 14, unify on (0).2 in 32 and (0).1 in 14
  subsumption eq52 eq32


@[equational_result]
theorem Equation3054_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3054 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X2) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq25 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.1.1 in 8
  have eq29 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq8 eq25 -- forward demodulation 25,8
  have eq66 (X0 : G) : (sK0 ◇ X0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) := superpose eq29 eq9 -- superposition 9,29, 29 into 9, unify on (0).2 in 29 and (0).1 in 9
  subsumption eq66 eq29


@[equational_result]
theorem Equation3054_implies_Equation4598 (G : Type*) [Magma G] (h : Equation3054 G) : Equation4598 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation2048_implies_Equation2668 (G : Type*) [Magma G] (h : Equation2048 G) : Equation2668 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) ◇ sK3) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq25 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK3) := superpose eq16 eq10 -- backward demodulation 10,16
  have eq26 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK3) := superpose eq16 eq25 -- forward demodulation 25,16
  subsumption eq26 eq13


@[equational_result]
theorem Equation442_implies_Equation359 (G : Type*) [Magma G] (h : Equation442 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq15 rfl


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
theorem Equation3929_implies_Equation4130 (G : Type*) [Magma G] (h : Equation3929 G) : Equation4130 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation3929_implies_Equation4136 (G : Type*) [Magma G] (h : Equation3929 G) : Equation4136 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK3) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation3929_implies_Equation3729 (G : Type*) [Magma G] (h : Equation3929 G) : Equation3729 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3929_implies_Equation3726 (G : Type*) [Magma G] (h : Equation3929 G) : Equation3726 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3929_implies_Equation3721 (G : Type*) [Magma G] (h : Equation3929 G) : Equation3721 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3929_implies_Equation4380 (G : Type*) [Magma G] (h : Equation3929 G) : Equation4380 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq9 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1 in 8
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq8 eq11 -- forward demodulation 11,8
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq9 -- backward demodulation 9,12
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2 in 12
  have eq25 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq17 eq13 -- superposition 13,17, 17 into 13, unify on (0).2 in 17 and (0).2 in 13
  subsumption eq25 rfl


@[equational_result]
theorem Equation3929_implies_Equation3722 (G : Type*) [Magma G] (h : Equation3929 G) : Equation3722 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3929_implies_Equation3723 (G : Type*) [Magma G] (h : Equation3929 G) : Equation3723 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3929_implies_Equation326 (G : Type*) [Magma G] (h : Equation3929 G) : Equation326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq27 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq27 rfl


@[equational_result]
theorem Equation3929_implies_Equation379 (G : Type*) [Magma G] (h : Equation3929 G) : Equation379 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3929_implies_Equation4474 (G : Type*) [Magma G] (h : Equation3929 G) : Equation4474 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq28 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).1 in 14
  subsumption eq28 rfl


@[equational_result]
theorem Equation3929_implies_Equation3523 (G : Type*) [Magma G] (h : Equation3929 G) : Equation3523 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq28 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq28 rfl


@[equational_result]
theorem Equation3929_implies_Equation3728 (G : Type*) [Magma G] (h : Equation3929 G) : Equation3728 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq20 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation3929_implies_Equation3724 (G : Type*) [Magma G] (h : Equation3929 G) : Equation3724 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


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
theorem Equation824_implies_Equation3256 (G : Type*) [Magma G] (h : Equation824 G) : Equation3256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq19 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq20 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq15 eq19 -- forward demodulation 19,15
  have eq24 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).1.2 in 9
  have eq39 : sK0 ≠ sK0 := superpose eq24 eq20 -- superposition 20,24, 24 into 20, unify on (0).2 in 24 and (0).2 in 20
  subsumption eq39 rfl


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
theorem Equation824_implies_Equation3257 (G : Type*) [Magma G] (h : Equation824 G) : Equation3257 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq19 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).1.2 in 9
  have eq38 : sK0 ≠ sK0 := superpose eq23 eq19 -- superposition 19,23, 23 into 19, unify on (0).2 in 23 and (0).2 in 19
  subsumption eq38 rfl


@[equational_result]
theorem Equation824_implies_Equation3918 (G : Type*) [Magma G] (h : Equation824 G) : Equation3918 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq29 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).1.2 in 9
  have eq35 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq29 eq10 -- backward demodulation 10,29
  subsumption eq35 rfl


@[equational_result]
theorem Equation824_implies_Equation417 (G : Type*) [Magma G] (h : Equation824 G) : Equation417 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq33 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).1.2 in 9
  have eq44 : sK0 ≠ sK0 := superpose eq33 eq10 -- superposition 10,33, 33 into 10, unify on (0).2 in 33 and (0).2 in 10
  subsumption eq44 rfl


@[equational_result]
theorem Equation824_implies_Equation1028 (G : Type*) [Magma G] (h : Equation824 G) : Equation1028 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X3 : G) : (X0 ◇ ((X0 ◇ X3) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq19 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq19 eq12


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
theorem Equation824_implies_Equation1025 (G : Type*) [Magma G] (h : Equation824 G) : Equation1025 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X3 : G) : (X0 ◇ ((X0 ◇ X3) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq25 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq25 rfl


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


