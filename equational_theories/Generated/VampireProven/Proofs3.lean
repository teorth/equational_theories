import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation3063_implies_Equation3072 (G : Type*) [Magma G] (h : Equation3063 G) : Equation3072 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK2) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1 in 14
  have eq37 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ X0) ◇ sK2) ◇ sK1) := superpose eq14 eq13 -- superposition 13,14, 14 into 13, unify on (0).2 in 14 and (0).2.1.1 in 13
  subsumption eq37 eq21


@[equational_result]
theorem Equation3063_implies_Equation4603 (G : Type*) [Magma G] (h : Equation3063 G) : Equation4603 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq20 (X0 : G) : ((sK0 ◇ X0) ◇ sK1) ≠ ((sK0 ◇ X0) ◇ sK2) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).1.1 in 13
  subsumption eq20 eq14


@[equational_result]
theorem Equation3090_implies_Equation3533 (G : Type*) [Magma G] (h : Equation3090 G) : Equation3533 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq25 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK1) ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq25 eq13


@[equational_result]
theorem Equation3090_implies_Equation4360 (G : Type*) [Magma G] (h : Equation3090 G) : Equation4360 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq111 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq111 eq13


@[equational_result]
theorem Equation3090_implies_Equation3063 (G : Type*) [Magma G] (h : Equation3090 G) : Equation3063 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq14 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK1) ◇ sK2) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq15 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK2) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq23 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).2 in 15
  subsumption eq23 eq9


@[equational_result]
theorem Equation3095_implies_Equation3464 (G : Type*) [Magma G] (h : Equation3095 G) : Equation3464 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq29 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ X0) ◇ sK0)) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.2.1 in 14
  subsumption eq29 eq13


@[equational_result]
theorem Equation3095_implies_Equation4597 (G : Type*) [Magma G] (h : Equation3095 G) : Equation4597 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 : G) : ((sK0 ◇ X0) ◇ sK1) ≠ ((sK0 ◇ X0) ◇ sK2) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).1.1 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation3095_implies_Equation3090 (G : Type*) [Magma G] (h : Equation3095 G) : Equation3090 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK1) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq9


@[equational_result]
theorem Equation3095_implies_Equation326 (G : Type*) [Magma G] (h : Equation3095 G) : Equation326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation3095_implies_Equation3078 (G : Type*) [Magma G] (h : Equation3095 G) : Equation3078 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X3) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq24 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK1) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq14


@[equational_result]
theorem Equation3095_implies_Equation3261 (G : Type*) [Magma G] (h : Equation3095 G) : Equation3261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation3095_implies_Equation4599 (G : Type*) [Magma G] (h : Equation3095 G) : Equation4599 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ X0) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation3095_implies_Equation4284 (G : Type*) [Magma G] (h : Equation3095 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation3095_implies_Equation3081 (G : Type*) [Magma G] (h : Equation3095 G) : Equation3081 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (((X0 ◇ X3) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK2) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq116 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK1) ◇ X0) ◇ X0) ◇ X0) := superpose eq11 eq24 -- superposition 24,11, 11 into 24, unify on (0).2 in 11 and (0).2 in 24
  subsumption eq116 eq9


@[equational_result]
theorem Equation3095_implies_Equation3315 (G : Type*) [Magma G] (h : Equation3095 G) : Equation3315 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ X0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation3095_implies_Equation4675 (G : Type*) [Magma G] (h : Equation3095 G) : Equation4675 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ X0) ◇ sK2) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation3072_implies_Equation3056 (G : Type*) [Magma G] (h : Equation3072 G) : Equation3056 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ X0) ◇ X3) ◇ X1) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq16 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ X1) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1.1 in 9
  have eq51 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ X0) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq51 eq16


@[equational_result]
theorem Equation3072_implies_Equation4633 (G : Type*) [Magma G] (h : Equation3072 G) : Equation4633 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 : ((sK0 ◇ sK0) ◇ sK2) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2 in 12
  have eq21 (X0 : G) : ((sK0 ◇ X0) ◇ sK2) ≠ ((sK0 ◇ X0) ◇ sK0) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  subsumption eq21 eq16


@[equational_result]
theorem Equation3072_implies_Equation3256 (G : Type*) [Magma G] (h : Equation3072 G) : Equation3256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation3072_implies_Equation3323 (G : Type*) [Magma G] (h : Equation3072 G) : Equation3323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation3072_implies_Equation3319 (G : Type*) [Magma G] (h : Equation3072 G) : Equation3319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation3072_implies_Equation3318 (G : Type*) [Magma G] (h : Equation3072 G) : Equation3318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation3072_implies_Equation3076 (G : Type*) [Magma G] (h : Equation3072 G) : Equation3076 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ X0) ◇ X3) ◇ X1) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq14 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ X1) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1.1 in 9
  have eq101 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ X0) ◇ sK1) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  subsumption eq101 eq16


@[equational_result]
theorem Equation3072_implies_Equation3095 (G : Type*) [Magma G] (h : Equation3072 G) : Equation3095 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ X0) ◇ X3) ◇ X1) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq14 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK2) ◇ sK2) ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq20 (X0 : G) : sK0 ≠ ((((sK0 ◇ X0) ◇ sK2) ◇ sK2) ◇ sK2) := superpose eq12 eq14 -- superposition 14,12, 12 into 14, unify on (0).2 in 12 and (0).2.1.1.1 in 14
  have eq60 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X4) ◇ X0) = ((((X0 ◇ X0) ◇ X2) ◇ X1) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq62 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq106 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X2) ◇ X1) ◇ X3) = X0 := superpose eq62 eq60 -- backward demodulation 60,62
  have eq367 : sK0 ≠ sK0 := superpose eq106 eq20 -- superposition 20,106, 106 into 20, unify on (0).2 in 106 and (0).2 in 20
  subsumption eq367 rfl


@[equational_result]
theorem Equation3072_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3072 G) : Equation3456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq16 rfl


@[equational_result]
theorem Equation3072_implies_Equation3055 (G : Type*) [Magma G] (h : Equation3072 G) : Equation3055 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ X0) ◇ X3) ◇ X1) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq19 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1.1 in 9
  have eq51 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ X0) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq51 eq19


@[equational_result]
theorem Equation3072_implies_Equation4316 (G : Type*) [Magma G] (h : Equation3072 G) : Equation4316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation3072_implies_Equation3058 (G : Type*) [Magma G] (h : Equation3072 G) : Equation3058 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ X0) ◇ X3) ◇ X1) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2 in 12
  have eq25 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X4) ◇ X0) = ((((X0 ◇ X0) ◇ X2) ◇ X1) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq27 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq57 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X2) ◇ X1) ◇ X3) = X0 := superpose eq27 eq25 -- backward demodulation 25,27
  have eq97 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK1) ◇ X0) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq97 eq57


@[equational_result]
theorem Equation3072_implies_Equation3265 (G : Type*) [Magma G] (h : Equation3072 G) : Equation3265 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation3072_implies_Equation3513 (G : Type*) [Magma G] (h : Equation3072 G) : Equation3513 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation3072_implies_Equation3259 (G : Type*) [Magma G] (h : Equation3072 G) : Equation3259 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation3072_implies_Equation3541 (G : Type*) [Magma G] (h : Equation3072 G) : Equation3541 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK3) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation3072_implies_Equation4629 (G : Type*) [Magma G] (h : Equation3072 G) : Equation4629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : ((sK0 ◇ sK0) ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2 in 12
  have eq20 (X0 : G) : ((sK0 ◇ X0) ◇ sK0) ≠ ((sK0 ◇ X0) ◇ sK1) := superpose eq12 eq14 -- superposition 14,12, 12 into 14, unify on (0).2 in 12 and (0).1.1 in 14
  subsumption eq20 eq15


@[equational_result]
theorem Equation3072_implies_Equation3470 (G : Type*) [Magma G] (h : Equation3072 G) : Equation3470 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK3)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation3072_implies_Equation3515 (G : Type*) [Magma G] (h : Equation3072 G) : Equation3515 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation3072_implies_Equation3512 (G : Type*) [Magma G] (h : Equation3072 G) : Equation3512 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation3072_implies_Equation3062 (G : Type*) [Magma G] (h : Equation3072 G) : Equation3062 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ X0) ◇ X3) ◇ X1) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2 in 12
  have eq25 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X4) ◇ X0) = ((((X0 ◇ X0) ◇ X2) ◇ X1) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq27 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq57 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X2) ◇ X1) ◇ X3) = X0 := superpose eq27 eq25 -- backward demodulation 25,27
  have eq97 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ X0) ◇ sK2) ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.1.1 in 10
  subsumption eq97 eq57


@[equational_result]
theorem Equation3072_implies_Equation3466 (G : Type*) [Magma G] (h : Equation3072 G) : Equation3466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation3072_implies_Equation4318 (G : Type*) [Magma G] (h : Equation3072 G) : Equation4318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation3072_implies_Equation3321 (G : Type*) [Magma G] (h : Equation3072 G) : Equation3321 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation3072_implies_Equation4282 (G : Type*) [Magma G] (h : Equation3072 G) : Equation4282 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation1868_implies_Equation1446 (G : Type*) [Magma G] (h : Equation1868 G) : Equation1446 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ (X3 ◇ (X4 ◇ X0))) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.2 in 11
  have eq50 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1868_implies_Equation4127 (G : Type*) [Magma G] (h : Equation1868 G) : Equation4127 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq21 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq98 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq98 rfl


@[equational_result]
theorem Equation1868_implies_Equation1427 (G : Type*) [Magma G] (h : Equation1868 G) : Equation1427 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ (X3 ◇ (X4 ◇ X0))) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.2 in 11
  have eq50 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1868_implies_Equation1445 (G : Type*) [Magma G] (h : Equation1868 G) : Equation1445 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ (X3 ◇ (X4 ◇ X0))) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.2 in 11
  have eq50 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1446_implies_Equation1868 (G : Type*) [Magma G] (h : Equation1446 G) : Equation1868 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation1446_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1446 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq19 rfl


@[equational_result]
theorem Equation1446_implies_Equation1442 (G : Type*) [Magma G] (h : Equation1446 G) : Equation1442 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq32 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1 in 16
  have eq138 : sK0 ≠ sK0 := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2 in 10
  subsumption eq138 rfl


@[equational_result]
theorem Equation1446_implies_Equation1858 (G : Type*) [Magma G] (h : Equation1446 G) : Equation1858 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation1446_implies_Equation1837 (G : Type*) [Magma G] (h : Equation1446 G) : Equation1837 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation1446_implies_Equation1838 (G : Type*) [Magma G] (h : Equation1446 G) : Equation1838 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq77 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq77 rfl


@[equational_result]
theorem Equation1446_implies_Equation1848 (G : Type*) [Magma G] (h : Equation1446 G) : Equation1848 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation1869_implies_Equation1448 (G : Type*) [Magma G] (h : Equation1869 G) : Equation1448 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).1.1 in 17
  have eq164 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq41 eq9 -- superposition 9,41, 41 into 9, unify on (0).2 in 41 and (0).1.1 in 9
  have eq234 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq164 eq164 -- superposition 164,164, 164 into 164, unify on (0).2 in 164 and (0).1.2 in 164
  have eq942 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq234 eq12 -- superposition 12,234, 234 into 12, unify on (0).2 in 234 and (0).2.2 in 12
  have eq963 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq164 eq942 -- forward demodulation 942,164
  have eq1132 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) = X2 := superpose eq963 eq9 -- superposition 9,963, 963 into 9, unify on (0).2 in 963 and (0).1.1.2 in 9
  have eq2222 : sK0 ≠ sK0 := superpose eq1132 eq10 -- superposition 10,1132, 1132 into 10, unify on (0).2 in 1132 and (0).2 in 10
  subsumption eq2222 rfl


@[equational_result]
theorem Equation1869_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1869 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq19 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq19 rfl


@[equational_result]
theorem Equation1869_implies_Equation1857 (G : Type*) [Magma G] (h : Equation1869 G) : Equation1857 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).1.1 in 17
  have eq164 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq41 eq9 -- superposition 9,41, 41 into 9, unify on (0).2 in 41 and (0).1.1 in 9
  have eq235 : sK0 ≠ sK0 := superpose eq164 eq10 -- superposition 10,164, 164 into 10, unify on (0).2 in 164 and (0).2 in 10
  subsumption eq235 rfl


@[equational_result]
theorem Equation1869_implies_Equation3511 (G : Type*) [Magma G] (h : Equation1869 G) : Equation3511 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).1.1 in 17
  have eq164 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq41 eq10 -- superposition 10,41, 41 into 10, unify on (0).2 in 41 and (0).2 in 10
  subsumption eq164 rfl


@[equational_result]
theorem Equation1869_implies_Equation1428 (G : Type*) [Magma G] (h : Equation1869 G) : Equation1428 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq55 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).2.2 in 12
  have eq318 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq55 eq16 -- superposition 16,55, 55 into 16, unify on (0).2 in 55 and (0).1.1 in 16
  have eq441 : sK0 ≠ sK0 := superpose eq318 eq10 -- superposition 10,318, 318 into 10, unify on (0).2 in 318 and (0).2 in 10
  subsumption eq441 rfl


@[equational_result]
theorem Equation1869_implies_Equation3457 (G : Type*) [Magma G] (h : Equation1869 G) : Equation3457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).1.1 in 17
  have eq47 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).2.2 in 12
  have eq164 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq41 eq9 -- superposition 9,41, 41 into 9, unify on (0).2 in 41 and (0).1.1 in 9
  have eq318 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq47 eq16 -- superposition 16,47, 47 into 16, unify on (0).2 in 47 and (0).1.1 in 16
  have eq424 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq164 eq318 -- superposition 318,164, 164 into 318, unify on (0).2 in 164 and (0).1.1 in 318
  have eq1566 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq424 eq10 -- superposition 10,424, 424 into 10, unify on (0).2 in 424 and (0).2 in 10
  subsumption eq1566 rfl


@[equational_result]
theorem Equation1869_implies_Equation1634 (G : Type*) [Magma G] (h : Equation1869 G) : Equation1634 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).1.1 in 17
  have eq164 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq41 eq9 -- superposition 9,41, 41 into 9, unify on (0).2 in 41 and (0).1.1 in 9
  have eq234 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq164 eq164 -- superposition 164,164, 164 into 164, unify on (0).2 in 164 and (0).1.2 in 164
  have eq942 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq234 eq12 -- superposition 12,234, 234 into 12, unify on (0).2 in 234 and (0).2.2 in 12
  have eq963 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq164 eq942 -- forward demodulation 942,164
  have eq1109 : sK0 ≠ sK0 := superpose eq963 eq10 -- superposition 10,963, 963 into 10, unify on (0).2 in 963 and (0).2 in 10
  subsumption eq1109 rfl


@[equational_result]
theorem Equation1869_implies_Equation1637 (G : Type*) [Magma G] (h : Equation1869 G) : Equation1637 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).1.1 in 17
  have eq164 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq41 eq9 -- superposition 9,41, 41 into 9, unify on (0).2 in 41 and (0).1.1 in 9
  have eq234 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq164 eq164 -- superposition 164,164, 164 into 164, unify on (0).2 in 164 and (0).1.2 in 164
  have eq913 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq234 eq12 -- superposition 12,234, 234 into 12, unify on (0).2 in 234 and (0).2.2 in 12
  have eq961 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq164 eq913 -- forward demodulation 913,164
  have eq1108 : sK0 ≠ sK0 := superpose eq961 eq10 -- superposition 10,961, 961 into 10, unify on (0).2 in 961 and (0).2 in 10
  subsumption eq1108 rfl


@[equational_result]
theorem Equation1869_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1869 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq16 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.2.2 in 10
  have eq40 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq10 eq16 -- superposition 16,10, 10 into 16, unify on (0).2 in 10 and (0).1.1 in 16
  have eq163 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq40 eq8 -- superposition 8,40, 40 into 8, unify on (0).2 in 40 and (0).1.1 in 8
  have eq233 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq163 eq163 -- superposition 163,163, 163 into 163, unify on (0).2 in 163 and (0).1.2 in 163
  have eq941 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq233 eq11 -- superposition 11,233, 233 into 11, unify on (0).2 in 233 and (0).2.2 in 11
  have eq962 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq163 eq941 -- forward demodulation 941,163
  have eq1108 : sK0 ≠ sK0 := superpose eq962 eq9 -- superposition 9,962, 962 into 9, unify on (0).2 in 962 and (0).2 in 9
  subsumption eq1108 rfl


@[equational_result]
theorem Equation1869_implies_Equation3459 (G : Type*) [Magma G] (h : Equation1869 G) : Equation3459 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X2))) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq76 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq17 eq13 -- superposition 13,17, 17 into 13, unify on (0).2 in 17 and (0).2.1 in 13
  have eq584 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq76 eq10 -- superposition 10,76, 76 into 10, unify on (0).2 in 76 and (0).2 in 10
  subsumption eq584 rfl


@[equational_result]
theorem Equation1869_implies_Equation3258 (G : Type*) [Magma G] (h : Equation1869 G) : Equation3258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).1.1 in 17
  have eq164 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq41 eq9 -- superposition 9,41, 41 into 9, unify on (0).2 in 41 and (0).1.1 in 9
  have eq235 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq164 eq12 -- superposition 12,164, 164 into 12, unify on (0).2 in 164 and (0).2.2 in 12
  have eq1365 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq235 eq10 -- superposition 10,235, 235 into 10, unify on (0).2 in 235 and (0).2 in 10
  subsumption eq1365 rfl


@[equational_result]
theorem Equation1869_implies_Equation1430 (G : Type*) [Magma G] (h : Equation1869 G) : Equation1430 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq47 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).2.2 in 12
  have eq317 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq47 eq16 -- superposition 16,47, 47 into 16, unify on (0).2 in 47 and (0).1.1 in 16
  have eq441 : sK0 ≠ sK0 := superpose eq317 eq10 -- superposition 10,317, 317 into 10, unify on (0).2 in 317 and (0).2 in 10
  subsumption eq441 rfl


@[equational_result]
theorem Equation1869_implies_Equation4067 (G : Type*) [Magma G] (h : Equation1869 G) : Equation4067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).1.1 in 17
  have eq164 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq41 eq9 -- superposition 9,41, 41 into 9, unify on (0).2 in 41 and (0).1.1 in 9
  have eq234 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq164 eq164 -- superposition 164,164, 164 into 164, unify on (0).2 in 164 and (0).1.2 in 164
  have eq918 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq234 eq10 -- superposition 10,234, 234 into 10, unify on (0).2 in 234 and (0).2 in 10
  subsumption eq918 rfl


@[equational_result]
theorem Equation1869_implies_Equation3259 (G : Type*) [Magma G] (h : Equation1869 G) : Equation3259 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq47 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).2.2 in 12
  have eq344 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq47 eq10 -- superposition 10,47, 47 into 10, unify on (0).2 in 47 and (0).2 in 10
  subsumption eq344 rfl


@[equational_result]
theorem Equation1869_implies_Equation1631 (G : Type*) [Magma G] (h : Equation1869 G) : Equation1631 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).1.1 in 17
  have eq164 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq41 eq9 -- superposition 9,41, 41 into 9, unify on (0).2 in 41 and (0).1.1 in 9
  have eq234 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq164 eq164 -- superposition 164,164, 164 into 164, unify on (0).2 in 164 and (0).1.2 in 164
  have eq913 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq234 eq12 -- superposition 12,234, 234 into 12, unify on (0).2 in 234 and (0).2.2 in 12
  have eq961 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq164 eq913 -- forward demodulation 913,164
  have eq1108 : sK0 ≠ sK0 := superpose eq961 eq10 -- superposition 10,961, 961 into 10, unify on (0).2 in 961 and (0).2 in 10
  subsumption eq1108 rfl


@[equational_result]
theorem Equation1869_implies_Equation1444 (G : Type*) [Magma G] (h : Equation1869 G) : Equation1444 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation1869_implies_Equation1868 (G : Type*) [Magma G] (h : Equation1869 G) : Equation1868 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq47 : sK0 ≠ sK0 := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation1869_implies_Equation1867 (G : Type*) [Magma G] (h : Equation1869 G) : Equation1867 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).1.1 in 17
  have eq164 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq41 eq9 -- superposition 9,41, 41 into 9, unify on (0).2 in 41 and (0).1.1 in 9
  have eq235 : sK0 ≠ sK0 := superpose eq164 eq10 -- superposition 10,164, 164 into 10, unify on (0).2 in 164 and (0).2 in 10
  subsumption eq235 rfl


@[equational_result]
theorem Equation1869_implies_Equation1640 (G : Type*) [Magma G] (h : Equation1869 G) : Equation1640 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).1.1 in 17
  have eq164 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq41 eq9 -- superposition 9,41, 41 into 9, unify on (0).2 in 41 and (0).1.1 in 9
  have eq234 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq164 eq164 -- superposition 164,164, 164 into 164, unify on (0).2 in 164 and (0).1.2 in 164
  have eq913 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq234 eq12 -- superposition 12,234, 234 into 12, unify on (0).2 in 234 and (0).2.2 in 12
  have eq961 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq164 eq913 -- forward demodulation 913,164
  have eq1108 : sK0 ≠ sK0 := superpose eq961 eq10 -- superposition 10,961, 961 into 10, unify on (0).2 in 961 and (0).2 in 10
  subsumption eq1108 rfl


@[equational_result]
theorem Equation1448_implies_Equation1869 (G : Type*) [Magma G] (h : Equation1448 G) : Equation1869 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq25 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1)))) ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq80 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq138 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.2 in 9
  have eq153 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq138 eq138 -- superposition 138,138, 138 into 138, unify on (0).2 in 138 and (0).1.1 in 138
  have eq433 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq153 eq9 -- superposition 9,153, 153 into 9, unify on (0).2 in 153 and (0).1.2 in 9
  have eq499 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq13 eq80 -- superposition 80,13, 13 into 80, unify on (0).2 in 13 and (0).2.2 in 80
  have eq537 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq433 eq499 -- forward demodulation 499,433
  have eq567 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) = X2 := superpose eq537 eq25 -- superposition 25,537, 537 into 25, unify on (0).2 in 537 and (0).1.1.2 in 25
  have eq1674 : sK0 ≠ sK0 := superpose eq567 eq10 -- superposition 10,567, 567 into 10, unify on (0).2 in 567 and (0).2 in 10
  subsumption eq1674 rfl


@[equational_result]
theorem Equation1448_implies_Equation151 (G : Type*) [Magma G] (h : Equation1448 G) : Equation151 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X0)) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1.1 in 11
  have eq137 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq8 -- superposition 8,17, 17 into 8, unify on (0).2 in 17 and (0).1.2 in 8
  have eq161 : sK0 ≠ sK0 := superpose eq137 eq9 -- superposition 9,137, 137 into 9, unify on (0).2 in 137 and (0).2 in 9
  subsumption eq161 rfl


@[equational_result]
theorem Equation1448_implies_Equation1429 (G : Type*) [Magma G] (h : Equation1448 G) : Equation1429 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq138 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.2 in 9
  have eq162 : sK0 ≠ sK0 := superpose eq138 eq10 -- superposition 10,138, 138 into 10, unify on (0).2 in 138 and (0).2 in 10
  subsumption eq162 rfl


@[equational_result]
theorem Equation212_implies_Equation160 (G : Type*) [Magma G] (h : Equation212 G) : Equation160 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq23 : sK0 ≠ sK0 := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq23 rfl


@[equational_result]
theorem Equation160_implies_Equation212 (G : Type*) [Magma G] (h : Equation160 G) : Equation212 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation160_implies_Equation203 (G : Type*) [Magma G] (h : Equation160 G) : Equation203 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq14 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq14 rfl


@[equational_result]
theorem Equation2278_implies_Equation2274 (G : Type*) [Magma G] (h : Equation2278 G) : Equation2274 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ X1) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation2278_implies_Equation1456 (G : Type*) [Magma G] (h : Equation2278 G) : Equation1456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ X1) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq53 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq53 rfl


@[equational_result]
theorem Equation2278_implies_Equation2246 (G : Type*) [Magma G] (h : Equation2278 G) : Equation2246 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ X1) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation2278_implies_Equation2249 (G : Type*) [Magma G] (h : Equation2278 G) : Equation2249 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ X1) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation2278_implies_Equation1428 (G : Type*) [Magma G] (h : Equation2278 G) : Equation1428 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ X1) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq53 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq53 rfl


@[equational_result]
theorem Equation2278_implies_Equation2286 (G : Type*) [Magma G] (h : Equation2278 G) : Equation2286 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ X1) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation2278_implies_Equation4314 (G : Type*) [Magma G] (h : Equation2278 G) : Equation4314 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ X1) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq62 (X0 X1 X4 X5 : G) : (X4 ◇ (X0 ◇ X1)) = (X4 ◇ (X0 ◇ X5)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).2.2.1 in 16
  have eq220 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq62 eq10 -- superposition 10,62, 62 into 10, unify on (0).2 in 62 and (0).2 in 10
  subsumption eq220 eq62


@[equational_result]
theorem Equation2278_implies_Equation1460 (G : Type*) [Magma G] (h : Equation2278 G) : Equation1460 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ X1) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq53 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq53 rfl


@[equational_result]
theorem Equation2278_implies_Equation3522 (G : Type*) [Magma G] (h : Equation2278 G) : Equation3522 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ X1) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq70 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq70 rfl


@[equational_result]
theorem Equation2274_implies_Equation2278 (G : Type*) [Magma G] (h : Equation2274 G) : Equation2278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ (X3 ◇ X0)) ◇ X3) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation2274_implies_Equation3460 (G : Type*) [Magma G] (h : Equation2274 G) : Equation3460 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ (X3 ◇ X0)) ◇ X3) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq56 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq56 rfl


@[equational_result]
theorem Equation2274_implies_Equation1457 (G : Type*) [Magma G] (h : Equation2274 G) : Equation1457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ (X3 ◇ X0)) ◇ X3) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq19 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X1)) = X2 := superpose eq15 eq12 -- backward demodulation 12,15
  have eq26 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation2274_implies_Equation3520 (G : Type*) [Magma G] (h : Equation2274 G) : Equation3520 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ (X3 ◇ X0)) ◇ X3) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq70 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq70 rfl


@[equational_result]
theorem Equation2274_implies_Equation4282 (G : Type*) [Magma G] (h : Equation2274 G) : Equation4282 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ (X3 ◇ X0)) ◇ X3) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq19 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X1)) = X2 := superpose eq15 eq12 -- backward demodulation 12,15
  have eq21 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq11 eq19 -- superposition 19,11, 11 into 19, unify on (0).2 in 11 and (0).1.1 in 19
  have eq102 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq102 eq21


@[equational_result]
theorem Equation1438_implies_Equation1436 (G : Type*) [Magma G] (h : Equation1438 G) : Equation1436 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq14 rfl


@[equational_result]
theorem Equation1859_implies_Equation1438 (G : Type*) [Magma G] (h : Equation1859 G) : Equation1438 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ (X2 ◇ X3)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq26 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq33 (X0 X2 : G) : (X2 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq26 -- superposition 26,9, 9 into 26, unify on (0).2 in 9 and (0).1.2 in 26
  have eq61 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := superpose eq33 eq10 -- backward demodulation 10,33
  have eq63 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq26 eq61 -- superposition 61,26, 26 into 61, unify on (0).2 in 26 and (0).2 in 61
  subsumption eq63 eq11


@[equational_result]
theorem Equation164_implies_Equation157 (G : Type*) [Magma G] (h : Equation164 G) : Equation157 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1882_implies_Equation1466 (G : Type*) [Magma G] (h : Equation1882 G) : Equation1466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ X0) ◇ (X5 ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X4 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq37 (X0 : G) : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ (X0 ◇ X0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq37 eq16


@[equational_result]
theorem Equation2283_implies_Equation3322 (G : Type*) [Magma G] (h : Equation2283 G) : Equation3322 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X2 ◇ (X3 ◇ X3))))) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X1 ◇ X2)) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq37 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (X0 ◇ X1)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq37 eq13


@[equational_result]
theorem Equation2283_implies_Equation1642 (G : Type*) [Magma G] (h : Equation2283 G) : Equation1642 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation2287_implies_Equation1878 (G : Type*) [Magma G] (h : Equation2287 G) : Equation1878 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X2 X5 : G) : ((X5 ◇ X0) ◇ X2) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation1854_implies_Equation1878 (G : Type*) [Magma G] (h : Equation1854 G) : Equation1878 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.2 in 12
  have eq26 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation2464_implies_Equation1844 (G : Type*) [Magma G] (h : Equation2464 G) : Equation1844 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq13 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq24 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 rfl


@[equational_result]
theorem Equation1652_implies_Equation2464 (G : Type*) [Magma G] (h : Equation1652 G) : Equation2464 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X3) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq23 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).2.2.1 in 11
  have eq30 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) := superpose eq23 eq10 -- backward demodulation 10,23
  have eq31 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq14 eq30 -- forward demodulation 30,14
  have eq88 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq23 eq23 -- superposition 23,23, 23 into 23, unify on (0).2 in 23 and (0).2 in 23
  have eq181 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq13 eq88 -- superposition 88,13, 13 into 88, unify on (0).2 in 13 and (0).1 in 88
  have eq222 (X0 : G) : sK0 ≠ ((sK0 ◇ sK0) ◇ X0) := superpose eq88 eq31 -- superposition 31,88, 88 into 31, unify on (0).2 in 88 and (0).2 in 31
  subsumption eq222 eq181


@[equational_result]
theorem Equation1466_implies_Equation1468 (G : Type*) [Magma G] (h : Equation1466 G) : Equation1468 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK3))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ X2)) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq14 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.2 in 12
  have eq37 (X0 X1 : G) : sK0 ≠ ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq37 eq14


@[equational_result]
theorem Equation2261_implies_Equation1642 (G : Type*) [Magma G] (h : Equation2261 G) : Equation1642 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation154_implies_Equation2261 (G : Type*) [Magma G] (h : Equation154 G) : Equation2261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq17 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq12


@[equational_result]
theorem Equation1846_implies_Equation3059 (G : Type*) [Magma G] (h : Equation1846 G) : Equation3059 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X4 X5 : G) : ((X4 ◇ (X4 ◇ X5)) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X4 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X4) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq22 (X0 X1 X4 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X4) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq78 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X0 := superpose eq22 eq13 -- superposition 13,22, 22 into 13, unify on (0).2 in 22 and (0).1.1 in 13
  have eq99 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq78 eq10 -- backward demodulation 10,78
  subsumption eq99 eq78


@[equational_result]
theorem Equation1846_implies_Equation1436 (G : Type*) [Magma G] (h : Equation1846 G) : Equation1436 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq13 (X0 X4 X5 : G) : ((X4 ◇ (X4 ◇ X5)) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X4 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X4) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq22 (X0 X1 X4 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X4) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq78 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X0 := superpose eq22 eq13 -- superposition 13,22, 22 into 13, unify on (0).2 in 22 and (0).1.1 in 13
  have eq88 (X0 : G) : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).2.2 in 10
  subsumption eq88 eq78


@[equational_result]
theorem Equation204_implies_Equation1846 (G : Type*) [Magma G] (h : Equation204 G) : Equation1846 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ X1) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK3)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq9


@[equational_result]
theorem Equation2288_implies_Equation204 (G : Type*) [Magma G] (h : Equation2288 G) : Equation204 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : ((X5 ◇ X0) ◇ X4) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation2288_implies_Equation154 (G : Type*) [Magma G] (h : Equation2288 G) : Equation154 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : ((X5 ◇ X0) ◇ X4) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation1433_implies_Equation1668 (G : Type*) [Magma G] (h : Equation1433 G) : Equation1668 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq18 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK1) ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq18 eq12


@[equational_result]
theorem Equation1433_implies_Equation2285 (G : Type*) [Magma G] (h : Equation1433 G) : Equation2285 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq18 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq18 eq12


@[equational_result]
theorem Equation1433_implies_Equation2261 (G : Type*) [Magma G] (h : Equation1433 G) : Equation2261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq18 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq19 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq14 eq18 -- forward demodulation 18,14
  subsumption eq19 eq12


@[equational_result]
theorem Equation157_implies_Equation3087 (G : Type*) [Magma G] (h : Equation157 G) : Equation3087 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK2) ◇ sK0) ◇ sK2) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq19 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq13 eq12 -- backward demodulation 12,13
  subsumption eq19 eq13


@[equational_result]
theorem Equation157_implies_Equation4120 (G : Type*) [Magma G] (h : Equation157 G) : Equation4120 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq19 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq12 -- backward demodulation 12,13
  subsumption eq19 rfl


@[equational_result]
theorem Equation157_implies_Equation1882 (G : Type*) [Magma G] (h : Equation157 G) : Equation1882 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK3 ◇ sK3)) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq16 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2 in 12
  subsumption eq16 eq9


@[equational_result]
theorem Equation1669_implies_Equation157 (G : Type*) [Magma G] (h : Equation1669 G) : Equation157 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ ((X2 ◇ X1) ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X2 ◇ X1) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ ((X2 ◇ X1) ◇ X1))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq15 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X1))) ◇ (X4 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X1)))) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2.1 in 12
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq21 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X1))) ◇ (X4 ◇ X1)) = X3 := superpose eq13 eq15 -- forward demodulation 15,13
  have eq22 (X1 X3 X4 : G) : ((X3 ◇ X1) ◇ (X4 ◇ X1)) = X3 := superpose eq13 eq21 -- forward demodulation 21,13
  have eq23 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq17 eq11 -- backward demodulation 11,17
  have eq32 (X0 : G) : sK0 ≠ ((sK0 ◇ X0) ◇ (sK0 ◇ X0)) := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2.1 in 10
  subsumption eq32 eq22


@[equational_result]
theorem Equation1669_implies_Equation2469 (G : Type*) [Magma G] (h : Equation1669 G) : Equation2469 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ ((X2 ◇ X1) ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X2 ◇ X1) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq23 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq17 eq11 -- backward demodulation 11,17
  have eq24 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X0 := superpose eq9 eq23 -- superposition 23,9, 9 into 23, unify on (0).2 in 9 and (0).1 in 23
  have eq62 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq24 eq10 -- backward demodulation 10,24
  subsumption eq62 eq24


@[equational_result]
theorem Equation1669_implies_Equation2275 (G : Type*) [Magma G] (h : Equation1669 G) : Equation2275 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ ((X2 ◇ X1) ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X2 ◇ X1) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq23 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq17 eq11 -- backward demodulation 11,17
  have eq24 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X0 := superpose eq9 eq23 -- superposition 23,9, 9 into 23, unify on (0).2 in 9 and (0).1 in 23
  have eq37 (X0 : G) : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq37 eq24


@[equational_result]
theorem Equation216_implies_Equation1669 (G : Type*) [Magma G] (h : Equation216 G) : Equation1669 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation1878_implies_Equation2491 (G : Type*) [Magma G] (h : Equation1878 G) : Equation2491 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK3)) ◇ sK3) := mod_symm nh
  have eq11 (X0 X2 X3 X4 X5 : G) : ((X4 ◇ X0) ◇ ((X2 ◇ X3) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ X0) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq23 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK3) := superpose eq18 eq10 -- backward demodulation 10,18
  subsumption eq23 eq18


@[equational_result]
theorem Equation1878_implies_Equation216 (G : Type*) [Magma G] (h : Equation1878 G) : Equation216 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 X4 X5 : G) : ((X4 ◇ X0) ◇ ((X2 ◇ X3) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ X0) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq41 (X0 X1 : G) : sK0 ≠ ((sK0 ◇ (X0 ◇ X1)) ◇ sK2) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq41 eq18


@[equational_result]
theorem Equation1878_implies_Equation1433 (G : Type*) [Magma G] (h : Equation1878 G) : Equation1433 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X2 X3 X4 X5 : G) : ((X4 ◇ X0) ◇ ((X2 ◇ X3) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X4 X5 X6 : G) : ((X4 ◇ X5) ◇ (X0 ◇ X6)) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq40 (X0 X1 : G) : sK0 ≠ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq40 eq16


@[equational_result]
theorem Equation1651_implies_Equation3051 (G : Type*) [Magma G] (h : Equation1651 G) : Equation3051 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq21 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq16 eq10 -- backward demodulation 10,16
  have eq31 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X1))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq32 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ X0)) := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).2.1 in 12
  have eq33 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2.1 in 12
  have eq44 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq33 eq32 -- backward demodulation 32,33
  have eq45 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq44 eq31 -- backward demodulation 31,44
  have eq50 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq45 eq45 -- superposition 45,45, 45 into 45, unify on (0).2 in 45 and (0).2 in 45
  have eq107 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X0 := superpose eq9 eq50 -- superposition 50,9, 9 into 50, unify on (0).2 in 9 and (0).1 in 50
  have eq142 (X0 : G) : sK0 ≠ ((sK0 ◇ X0) ◇ sK1) := superpose eq50 eq21 -- superposition 21,50, 50 into 21, unify on (0).2 in 50 and (0).2.1 in 21
  subsumption eq142 eq107


@[equational_result]
theorem Equation1651_implies_Equation1878 (G : Type*) [Magma G] (h : Equation1651 G) : Equation1878 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X1))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq25 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ X0)) := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).2.1 in 12
  have eq35 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2.1 in 12
  have eq43 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ X0) := superpose eq35 eq25 -- backward demodulation 25,35
  have eq45 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq43 eq24 -- backward demodulation 24,43
  have eq48 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK3)) := superpose eq45 eq10 -- backward demodulation 10,45
  have eq49 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK2 ◇ sK3)) := superpose eq35 eq48 -- forward demodulation 48,35
  have eq51 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq45 eq45 -- superposition 45,45, 45 into 45, unify on (0).2 in 45 and (0).2 in 45
  have eq108 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X0 := superpose eq9 eq51 -- superposition 51,9, 9 into 51, unify on (0).2 in 9 and (0).1 in 51
  have eq138 (X0 : G) : sK0 ≠ ((sK0 ◇ sK0) ◇ X0) := superpose eq51 eq49 -- superposition 49,51, 51 into 49, unify on (0).2 in 51 and (0).2 in 49
  subsumption eq138 eq108


@[equational_result]
theorem Equation1666_implies_Equation2257 (G : Type*) [Magma G] (h : Equation1666 G) : Equation2257 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.1 in 11
  have eq81 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X3) ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).2.2.1 in 11
  have eq115 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq11 eq81 -- superposition 81,11, 11 into 81, unify on (0).2 in 11 and (0).1.1 in 81
  have eq172 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq115 eq9 -- backward demodulation 9,115
  have eq183 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) := superpose eq115 eq94 -- backward demodulation 94,115
  have eq212 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) := superpose eq115 eq183 -- forward demodulation 183,115
  have eq213 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq172 eq212 -- forward demodulation 212,172
  have eq216 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq213 eq10 -- backward demodulation 10,213
  subsumption eq216 eq172


@[equational_result]
theorem Equation1666_implies_Equation2253 (G : Type*) [Magma G] (h : Equation1666 G) : Equation2253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.1 in 11
  have eq81 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X3) ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).2.2.1 in 11
  have eq115 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq11 eq81 -- superposition 81,11, 11 into 81, unify on (0).2 in 11 and (0).1.1 in 81
  have eq172 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq115 eq9 -- backward demodulation 9,115
  have eq183 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) := superpose eq115 eq94 -- backward demodulation 94,115
  have eq212 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) := superpose eq115 eq183 -- forward demodulation 183,115
  have eq213 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq172 eq212 -- forward demodulation 212,172
  have eq216 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq213 eq10 -- backward demodulation 10,213
  subsumption eq216 eq115


@[equational_result]
theorem Equation1666_implies_Equation2283 (G : Type*) [Magma G] (h : Equation1666 G) : Equation2283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.1 in 11
  have eq81 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X3) ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).2.2.1 in 11
  have eq115 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq11 eq81 -- superposition 81,11, 11 into 81, unify on (0).2 in 11 and (0).1.1 in 81
  have eq172 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq115 eq9 -- backward demodulation 9,115
  have eq183 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) := superpose eq115 eq94 -- backward demodulation 94,115
  have eq212 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) := superpose eq115 eq183 -- forward demodulation 183,115
  have eq213 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq172 eq212 -- forward demodulation 212,172
  have eq216 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq213 eq10 -- backward demodulation 10,213
  subsumption eq216 eq172


@[equational_result]
theorem Equation1844_implies_Equation3067 (G : Type*) [Magma G] (h : Equation1844 G) : Equation3067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ (X2 ◇ X1))) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq30 (X0 X3 X4 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ X4) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2.2 in 13
  have eq34 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq54 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X3) := superpose eq30 eq34 -- forward demodulation 34,30
  have eq155 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X0 := superpose eq54 eq30 -- superposition 30,54, 54 into 30, unify on (0).2 in 54 and (0).1.1 in 30
  have eq185 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq155 eq10 -- backward demodulation 10,155
  subsumption eq185 eq155


@[equational_result]
theorem Equation1844_implies_Equation1669 (G : Type*) [Magma G] (h : Equation1844 G) : Equation1669 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ (X2 ◇ X1))) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq31 (X0 X3 X4 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ X4) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2.2 in 13
  have eq35 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq55 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X3) := superpose eq31 eq35 -- forward demodulation 35,31
  have eq155 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X0 := superpose eq55 eq31 -- superposition 31,55, 55 into 31, unify on (0).2 in 55 and (0).1.1 in 31
  have eq187 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq155 eq10 -- backward demodulation 10,155
  subsumption eq187 eq155


@[equational_result]
theorem Equation2478_implies_Equation164 (G : Type*) [Magma G] (h : Equation2478 G) : Equation164 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq23 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq23 rfl


@[equational_result]
theorem Equation2478_implies_Equation1855 (G : Type*) [Magma G] (h : Equation2478 G) : Equation1855 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation1436_implies_Equation2478 (G : Type*) [Magma G] (h : Equation1436 G) : Equation2478 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq19 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq19 eq12


@[equational_result]
theorem Equation1436_implies_Equation1841 (G : Type*) [Magma G] (h : Equation1436 G) : Equation1841 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq19 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq19 eq12


@[equational_result]
theorem Equation1642_implies_Equation1859 (G : Type*) [Magma G] (h : Equation1642 G) : Equation1859 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 (X0 X3 : G) : ((X3 ◇ X3) ◇ X0) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq24 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq18 eq18 -- superposition 18,18, 18 into 18, unify on (0).2 in 18 and (0).1.1 in 18
  have eq32 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := superpose eq24 eq10 -- backward demodulation 10,24
  have eq33 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq24 eq32 -- forward demodulation 32,24
  subsumption eq33 eq18


@[equational_result]
theorem Equation1468_implies_Equation3098 (G : Type*) [Magma G] (h : Equation1468 G) : Equation3098 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK3) ◇ sK1) := mod_symm nh
  have eq13 (X0 X2 X4 : G) : ((X4 ◇ X2) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ sK3) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation1468_implies_Equation1842 (G : Type*) [Magma G] (h : Equation1468 G) : Equation1842 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq13 (X0 X2 X4 : G) : ((X4 ◇ X2) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation1468_implies_Equation2484 (G : Type*) [Magma G] (h : Equation1468 G) : Equation2484 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X2 X4 : G) : ((X4 ◇ X2) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation1468_implies_Equation1666 (G : Type*) [Magma G] (h : Equation1468 G) : Equation1666 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq13 (X0 X2 X4 : G) : ((X4 ◇ X2) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation1468_implies_Equation4078 (G : Type*) [Magma G] (h : Equation1468 G) : Equation4078 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq13 (X0 X2 X4 : G) : ((X4 ◇ X2) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X0 X1 X4 : G) : (X0 ◇ X1) = (X0 ◇ X4) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq35 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2 in 15
  subsumption eq35 eq16


@[equational_result]
theorem Equation2453_implies_Equation3086 (G : Type*) [Magma G] (h : Equation2453 G) : Equation3086 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2.1 in 9
  have eq19 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X4)) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq20 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = ((((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X4)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.1 in 11
  have eq33 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ X0) ◇ (X0 ◇ X3)) := superpose eq18 eq20 -- forward demodulation 20,18
  have eq34 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq12 eq33 -- forward demodulation 33,12
  have eq36 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ X0) := superpose eq34 eq18 -- backward demodulation 18,34
  have eq37 (X0 X1 X3 X4 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = ((((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X4)) ◇ X1) := superpose eq36 eq19 -- backward demodulation 19,36
  have eq39 (X0 X1 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ X1) := superpose eq36 eq11 -- backward demodulation 11,36
  have eq41 (X0 X1 X4 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X4)) ◇ X1) = X0 := superpose eq34 eq37 -- forward demodulation 37,34
  have eq42 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq36 eq41 -- forward demodulation 41,36
  have eq43 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq34 eq39 -- forward demodulation 39,34
  have eq44 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK2) ◇ sK0) ◇ sK1) := superpose eq43 eq10 -- backward demodulation 10,43
  have eq45 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq42 eq44 -- forward demodulation 44,42
  subsumption eq45 eq42


@[equational_result]
theorem Equation2453_implies_Equation2462 (G : Type*) [Magma G] (h : Equation2453 G) : Equation2462 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2.1 in 9
  have eq20 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = ((((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X4)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.1 in 11
  have eq33 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ X0) ◇ (X0 ◇ X3)) := superpose eq18 eq20 -- forward demodulation 20,18
  have eq34 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq12 eq33 -- forward demodulation 33,12
  have eq36 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ X0) := superpose eq34 eq18 -- backward demodulation 18,34
  have eq39 (X0 X1 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ X1) := superpose eq36 eq11 -- backward demodulation 11,36
  have eq43 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq34 eq39 -- forward demodulation 39,34
  have eq44 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq43 eq10 -- backward demodulation 10,43
  subsumption eq44 eq15


@[equational_result]
theorem Equation2453_implies_Equation4150 (G : Type*) [Magma G] (h : Equation2453 G) : Equation4150 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK3) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2.1 in 9
  have eq19 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X4)) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq20 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = ((((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X4)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.1 in 11
  have eq33 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ X0) ◇ (X0 ◇ X3)) := superpose eq18 eq20 -- forward demodulation 20,18
  have eq34 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq12 eq33 -- forward demodulation 33,12
  have eq36 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ X0) := superpose eq34 eq18 -- backward demodulation 18,34
  have eq37 (X0 X1 X3 X4 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = ((((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X4)) ◇ X1) := superpose eq36 eq19 -- backward demodulation 19,36
  have eq39 (X0 X1 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ X1) := superpose eq36 eq11 -- backward demodulation 11,36
  have eq41 (X0 X1 X4 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X4)) ◇ X1) = X0 := superpose eq34 eq37 -- forward demodulation 37,34
  have eq42 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq36 eq41 -- forward demodulation 41,36
  have eq43 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq34 eq39 -- forward demodulation 39,34
  have eq44 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK3) ◇ sK1) := superpose eq43 eq10 -- backward demodulation 10,43
  have eq45 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq42 eq44 -- forward demodulation 44,42
  subsumption eq45 rfl


@[equational_result]
theorem Equation2453_implies_Equation2277 (G : Type*) [Magma G] (h : Equation2453 G) : Equation2277 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2.1 in 9
  have eq20 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = ((((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X4)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.1 in 11
  have eq33 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ X0) ◇ (X0 ◇ X3)) := superpose eq18 eq20 -- forward demodulation 20,18
  have eq34 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq12 eq33 -- forward demodulation 33,12
  have eq36 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ X0) := superpose eq34 eq18 -- backward demodulation 18,34
  have eq39 (X0 X1 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ X1) := superpose eq36 eq11 -- backward demodulation 11,36
  have eq43 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq34 eq39 -- forward demodulation 39,34
  have eq44 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq43 eq10 -- backward demodulation 10,43
  subsumption eq44 eq15


@[equational_result]
theorem Equation2453_implies_Equation4076 (G : Type*) [Magma G] (h : Equation2453 G) : Equation4076 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2.1 in 9
  have eq19 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X4)) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq20 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = ((((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X4)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.1 in 11
  have eq33 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ X0) ◇ (X0 ◇ X3)) := superpose eq18 eq20 -- forward demodulation 20,18
  have eq34 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq12 eq33 -- forward demodulation 33,12
  have eq36 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ X0) := superpose eq34 eq18 -- backward demodulation 18,34
  have eq37 (X0 X1 X3 X4 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = ((((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X4)) ◇ X1) := superpose eq36 eq19 -- backward demodulation 19,36
  have eq39 (X0 X1 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ X1) := superpose eq36 eq11 -- backward demodulation 11,36
  have eq41 (X0 X1 X4 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X4)) ◇ X1) = X0 := superpose eq34 eq37 -- forward demodulation 37,34
  have eq42 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq36 eq41 -- forward demodulation 41,36
  have eq43 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq34 eq39 -- forward demodulation 39,34
  have eq44 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK2) ◇ sK0) := superpose eq43 eq10 -- backward demodulation 10,43
  have eq45 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq42 eq44 -- forward demodulation 44,42
  subsumption eq45 rfl


@[equational_result]
theorem Equation2453_implies_Equation4138 (G : Type*) [Magma G] (h : Equation2453 G) : Equation4138 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2.1 in 9
  have eq20 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = ((((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X4)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.1 in 11
  have eq33 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ X0) ◇ (X0 ◇ X3)) := superpose eq18 eq20 -- forward demodulation 20,18
  have eq34 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq12 eq33 -- forward demodulation 33,12
  have eq36 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ X0) := superpose eq34 eq18 -- backward demodulation 18,34
  have eq39 (X0 X1 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ X1) := superpose eq36 eq11 -- backward demodulation 11,36
  have eq43 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq34 eq39 -- forward demodulation 39,34
  have eq44 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := superpose eq43 eq10 -- backward demodulation 10,43
  have eq45 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq44 -- forward demodulation 44,15
  subsumption eq45 rfl


@[equational_result]
theorem Equation2453_implies_Equation2287 (G : Type*) [Magma G] (h : Equation2453 G) : Equation2287 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2.1 in 9
  have eq19 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X4)) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq20 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = ((((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X4)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.1 in 11
  have eq33 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ X0) ◇ (X0 ◇ X3)) := superpose eq18 eq20 -- forward demodulation 20,18
  have eq34 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq12 eq33 -- forward demodulation 33,12
  have eq36 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ X0) := superpose eq34 eq18 -- backward demodulation 18,34
  have eq37 (X0 X1 X3 X4 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = ((((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X4)) ◇ X1) := superpose eq36 eq19 -- backward demodulation 19,36
  have eq39 (X0 X1 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ X1) := superpose eq36 eq11 -- backward demodulation 11,36
  have eq41 (X0 X1 X4 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X4)) ◇ X1) = X0 := superpose eq34 eq37 -- forward demodulation 37,34
  have eq42 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq36 eq41 -- forward demodulation 41,36
  have eq43 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq34 eq39 -- forward demodulation 39,34
  have eq44 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq43 eq10 -- backward demodulation 10,43
  subsumption eq44 eq42


@[equational_result]
theorem Equation1877_implies_Equation2247 (G : Type*) [Magma G] (h : Equation1877 G) : Equation2247 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq22 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq33 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.1 in 11
  have eq35 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq44 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq35 eq33 -- backward demodulation 33,35
  have eq46 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X0) = X2 := superpose eq44 eq22 -- backward demodulation 22,44
  have eq47 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X2 ◇ X0) := superpose eq44 eq16 -- backward demodulation 16,44
  have eq54 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq47 eq46 -- backward demodulation 46,47
  have eq55 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq47 eq10 -- backward demodulation 10,47
  subsumption eq55 eq54


@[equational_result]
theorem Equation1877_implies_Equation1647 (G : Type*) [Magma G] (h : Equation1877 G) : Equation1647 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq33 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.1 in 11
  have eq35 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq44 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq35 eq33 -- backward demodulation 33,35
  have eq49 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq44 eq11 -- backward demodulation 11,44
  have eq57 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq49 eq10 -- backward demodulation 10,49
  subsumption eq57 eq49


@[equational_result]
theorem Equation1877_implies_Equation4070 (G : Type*) [Magma G] (h : Equation1877 G) : Equation4070 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq32 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.1 in 11
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq43 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq34 eq32 -- backward demodulation 32,34
  have eq48 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq43 eq11 -- backward demodulation 11,43
  have eq56 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq48 eq10 -- backward demodulation 10,48
  subsumption eq56 rfl


@[equational_result]
theorem Equation1877_implies_Equation2266 (G : Type*) [Magma G] (h : Equation1877 G) : Equation2266 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq33 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.1 in 11
  have eq35 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq44 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq35 eq33 -- backward demodulation 33,35
  have eq47 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X2 ◇ X0) := superpose eq44 eq16 -- backward demodulation 16,44
  have eq49 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq44 eq11 -- backward demodulation 11,44
  have eq55 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq47 eq10 -- backward demodulation 10,47
  have eq65 : sK0 ≠ sK0 := superpose eq49 eq55 -- superposition 55,49, 49 into 55, unify on (0).2 in 49 and (0).2 in 55
  subsumption eq65 rfl


@[equational_result]
theorem Equation1877_implies_Equation215 (G : Type*) [Magma G] (h : Equation1877 G) : Equation215 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq32 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.1 in 11
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq43 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq34 eq32 -- backward demodulation 32,34
  have eq48 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq43 eq11 -- backward demodulation 11,43
  have eq62 : sK0 ≠ sK0 := superpose eq48 eq10 -- superposition 10,48, 48 into 10, unify on (0).2 in 48 and (0).2 in 10
  subsumption eq62 rfl


@[equational_result]
theorem Equation1877_implies_Equation1638 (G : Type*) [Magma G] (h : Equation1877 G) : Equation1638 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq22 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq33 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.1 in 11
  have eq35 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq44 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq35 eq33 -- backward demodulation 33,35
  have eq46 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X0) = X2 := superpose eq44 eq22 -- backward demodulation 22,44
  have eq47 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X2 ◇ X0) := superpose eq44 eq16 -- backward demodulation 16,44
  have eq49 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq44 eq11 -- backward demodulation 11,44
  have eq54 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq47 eq46 -- backward demodulation 46,47
  have eq55 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq54 eq10 -- backward demodulation 10,54
  have eq64 : sK0 ≠ sK0 := superpose eq49 eq55 -- superposition 55,49, 49 into 55, unify on (0).2 in 49 and (0).2 in 55
  subsumption eq64 rfl


@[equational_result]
theorem Equation1877_implies_Equation1455 (G : Type*) [Magma G] (h : Equation1877 G) : Equation1455 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq33 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.1 in 11
  have eq35 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq44 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq35 eq33 -- backward demodulation 33,35
  have eq49 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq44 eq11 -- backward demodulation 11,44
  have eq70 : sK0 ≠ sK0 := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2 in 10
  subsumption eq70 rfl


@[equational_result]
theorem Equation1877_implies_Equation1834 (G : Type*) [Magma G] (h : Equation1877 G) : Equation1834 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq23 eq9


@[equational_result]
theorem Equation1877_implies_Equation2472 (G : Type*) [Magma G] (h : Equation1877 G) : Equation2472 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq28 (X0 : G) : sK0 ≠ ((sK0 ◇ (X0 ◇ sK2)) ◇ sK0) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.1 in 13
  have eq36 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.1 in 11
  have eq38 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq47 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq38 eq36 -- backward demodulation 36,38
  have eq49 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq47 eq11 -- backward demodulation 11,47
  have eq65 : sK0 ≠ sK0 := superpose eq49 eq28 -- superposition 28,49, 49 into 28, unify on (0).2 in 49 and (0).2 in 28
  subsumption eq65 rfl


@[equational_result]
theorem Equation1877_implies_Equation206 (G : Type*) [Magma G] (h : Equation1877 G) : Equation206 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq32 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.1 in 11
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq43 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq34 eq32 -- backward demodulation 32,34
  have eq48 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq43 eq11 -- backward demodulation 11,43
  have eq62 : sK0 ≠ sK0 := superpose eq48 eq10 -- superposition 10,48, 48 into 10, unify on (0).2 in 48 and (0).2 in 10
  subsumption eq62 rfl


@[equational_result]
theorem Equation1877_implies_Equation4141 (G : Type*) [Magma G] (h : Equation1877 G) : Equation4141 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq32 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.1 in 11
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq43 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq34 eq32 -- backward demodulation 32,34
  have eq47 (X0 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ X2) := superpose eq43 eq13 -- backward demodulation 13,43
  have eq48 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq43 eq11 -- backward demodulation 11,43
  have eq56 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq48 eq10 -- backward demodulation 10,48
  subsumption eq56 eq47


@[equational_result]
theorem Equation1877_implies_Equation157 (G : Type*) [Magma G] (h : Equation1877 G) : Equation157 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq32 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.1 in 11
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq43 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq34 eq32 -- backward demodulation 32,34
  have eq48 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq43 eq11 -- backward demodulation 11,43
  have eq62 : sK0 ≠ sK0 := superpose eq48 eq10 -- superposition 10,48, 48 into 10, unify on (0).2 in 48 and (0).2 in 10
  subsumption eq62 rfl


@[equational_result]
theorem Equation1877_implies_Equation1443 (G : Type*) [Magma G] (h : Equation1877 G) : Equation1443 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq32 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.1 in 11
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq43 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq34 eq32 -- backward demodulation 32,34
  have eq48 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq43 eq11 -- backward demodulation 11,43
  have eq62 : sK0 ≠ sK0 := superpose eq48 eq10 -- superposition 10,48, 48 into 10, unify on (0).2 in 48 and (0).2 in 10
  subsumption eq62 rfl


