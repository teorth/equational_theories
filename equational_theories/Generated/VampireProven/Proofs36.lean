import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation4465_implies_Equation4442 (G : Type*) [Magma G] (h : Equation4465 G) : Equation4442 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X2 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK0 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq201 (X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X5 ◇ (X4 ◇ X5))) := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1 in 12
  have eq233 (X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X2 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).2 in 19
  subsumption eq233 eq201


@[equational_result]
theorem Equation4465_implies_Equation4383 (G : Type*) [Magma G] (h : Equation4465 G) : Equation4383 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X2 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq201 (X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X5 ◇ (X4 ◇ X5))) := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1 in 12
  have eq233 (X2 X3 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X2 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).2 in 19
  subsumption eq233 eq201


@[equational_result]
theorem Equation4465_implies_Equation4440 (G : Type*) [Magma G] (h : Equation4465 G) : Equation4440 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X2 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq201 (X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X5 ◇ (X4 ◇ X5))) := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1 in 12
  have eq233 (X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X2 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).2 in 19
  subsumption eq233 eq201


@[equational_result]
theorem Equation4465_implies_Equation4393 (G : Type*) [Magma G] (h : Equation4465 G) : Equation4393 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X2 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq201 (X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X5 ◇ (X4 ◇ X5))) := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1 in 12
  have eq233 (X2 X3 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X2 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).2 in 19
  subsumption eq233 eq201


@[equational_result]
theorem Equation3296_implies_Equation3278 (G : Type*) [Magma G] (h : Equation3296 G) : Equation3278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq17 (X0 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq24 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq24 rfl


@[equational_result]
theorem Equation3296_implies_Equation3288 (G : Type*) [Magma G] (h : Equation3296 G) : Equation3288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq17 (X0 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq27 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq27 rfl


@[equational_result]
theorem Equation4110_implies_Equation3663 (G : Type*) [Magma G] (h : Equation4110 G) : Equation3663 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq24 (X0 : G) : (X0 ◇ X0) ≠ ((X0 ◇ X0) ◇ (sK1 ◇ sK2)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).1 in 10
  subsumption eq24 eq14


@[equational_result]
theorem Equation4110_implies_Equation3690 (G : Type*) [Magma G] (h : Equation4110 G) : Equation3690 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (sK2 ◇ sK0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq24 eq14


@[equational_result]
theorem Equation4110_implies_Equation4091 (G : Type*) [Magma G] (h : Equation4110 G) : Equation4091 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq47 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.1 in 10
  subsumption eq47 eq14


@[equational_result]
theorem Equation4110_implies_Equation4069 (G : Type*) [Magma G] (h : Equation4110 G) : Equation4069 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq47 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK2) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.1 in 10
  subsumption eq47 eq14


@[equational_result]
theorem Equation4110_implies_Equation4067 (G : Type*) [Magma G] (h : Equation4110 G) : Equation4067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq47 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK0) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.1 in 10
  subsumption eq47 eq14


@[equational_result]
theorem Equation4110_implies_Equation4096 (G : Type*) [Magma G] (h : Equation4110 G) : Equation4096 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq47 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK0) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.1 in 10
  subsumption eq47 eq14


@[equational_result]
theorem Equation4110_implies_Equation4591 (G : Type*) [Magma G] (h : Equation4110 G) : Equation4591 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq47 (X0 : G) : (X0 ◇ X0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq47 eq14


@[equational_result]
theorem Equation4110_implies_Equation4597 (G : Type*) [Magma G] (h : Equation4110 G) : Equation4597 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq47 (X0 : G) : (X0 ◇ X0) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq47 eq14


@[equational_result]
theorem Equation4110_implies_Equation360 (G : Type*) [Magma G] (h : Equation4110 G) : Equation360 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq22 (X0 : G) : (X0 ◇ X0) ≠ ((X0 ◇ X0) ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).1 in 10
  subsumption eq22 eq14


@[equational_result]
theorem Equation4110_implies_Equation3693 (G : Type*) [Magma G] (h : Equation4110 G) : Equation3693 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (sK2 ◇ sK3)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq24 eq14


@[equational_result]
theorem Equation4110_implies_Equation3660 (G : Type*) [Magma G] (h : Equation4110 G) : Equation3660 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq22 (X0 : G) : (X0 ◇ X0) ≠ ((X0 ◇ X0) ◇ (sK0 ◇ sK1)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).1 in 10
  subsumption eq22 eq14


@[equational_result]
theorem Equation4110_implies_Equation4623 (G : Type*) [Magma G] (h : Equation4110 G) : Equation4623 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ sK3) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq47 (X0 : G) : (X0 ◇ X0) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq47 eq14


@[equational_result]
theorem Equation4110_implies_Equation4099 (G : Type*) [Magma G] (h : Equation4110 G) : Equation4099 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq47 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK3) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.1 in 10
  subsumption eq47 eq14


@[equational_result]
theorem Equation4110_implies_Equation4066 (G : Type*) [Magma G] (h : Equation4110 G) : Equation4066 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq52 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.1 in 10
  subsumption eq52 eq14


@[equational_result]
theorem Equation4110_implies_Equation3661 (G : Type*) [Magma G] (h : Equation4110 G) : Equation3661 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq24 (X0 : G) : (X0 ◇ X0) ≠ ((X0 ◇ X0) ◇ (sK1 ◇ sK0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).1 in 10
  subsumption eq24 eq14


@[equational_result]
theorem Equation4454_implies_Equation4591 (G : Type*) [Magma G] (h : Equation4454 G) : Equation4591 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 : G) : ((sK0 ◇ sK0) ◇ sK0) ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq24 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq95 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ X3) = (X4 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X2))) := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).2.2.2 in 12
  have eq192 (X1 X2 : G) : ((sK0 ◇ sK0) ◇ sK0) ≠ ((X1 ◇ (X2 ◇ X1)) ◇ (sK1 ◇ X1)) := superpose eq15 eq17 -- superposition 17,15, 15 into 17, unify on (0).2 in 15 and (0).2 in 17
  have eq3130 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X3) ◇ X4) = ((X5 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X5) := superpose eq24 eq95 -- superposition 95,24, 24 into 95, unify on (0).2 in 24 and (0).2 in 95
  have eq3271 (X0 X1 X2 X3 : G) : ((sK0 ◇ sK0) ◇ sK0) ≠ ((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X3) := superpose eq95 eq192 -- superposition 192,95, 95 into 192, unify on (0).2 in 95 and (0).2 in 192
  subsumption eq3271 eq3130


@[equational_result]
theorem Equation4454_implies_Equation4636 (G : Type*) [Magma G] (h : Equation4454 G) : Equation4636 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq24 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq95 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ X3) = (X4 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X2))) := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).2.2.2 in 12
  have eq199 (X1 X2 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ ((X1 ◇ (X2 ◇ X1)) ◇ (sK0 ◇ X1)) := superpose eq15 eq17 -- superposition 17,15, 15 into 17, unify on (0).2 in 15 and (0).2 in 17
  have eq3130 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X3) ◇ X4) = ((X5 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X5) := superpose eq24 eq95 -- superposition 95,24, 24 into 95, unify on (0).2 in 24 and (0).2 in 95
  have eq3315 (X0 X1 X2 X3 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ ((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X3) := superpose eq95 eq199 -- superposition 199,95, 95 into 199, unify on (0).2 in 95 and (0).2 in 199
  subsumption eq3315 eq3130


@[equational_result]
theorem Equation4454_implies_Equation4336 (G : Type*) [Magma G] (h : Equation4454 G) : Equation4336 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK3 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = (X1 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq32 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = (((X2 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2.1 in 9
  have eq60 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (X0 ◇ sK2)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  have eq72 (X1 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((X1 ◇ sK2) ◇ X1) := superpose eq9 eq60 -- superposition 60,9, 9 into 60, unify on (0).2 in 9 and (0).2 in 60
  have eq73 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X0) = ((X1 ◇ X0) ◇ (X3 ◇ (X4 ◇ X3))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq4155 (X0 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X2)) = ((X0 ◇ (X4 ◇ X0)) ◇ X0) := superpose eq32 eq73 -- superposition 73,32, 32 into 73, unify on (0).2 in 32 and (0).2 in 73
  have eq4291 (X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ (X2 ◇ sK2)) ◇ sK2) := superpose eq73 eq72 -- superposition 72,73, 73 into 72, unify on (0).2 in 73 and (0).2 in 72
  subsumption eq4291 eq4155


@[equational_result]
theorem Equation4454_implies_Equation4458 (G : Type*) [Magma G] (h : Equation4454 G) : Equation4458 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq19 (X1 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((X1 ◇ sK1) ◇ X1) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq36 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = (((X2 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2.1 in 9
  have eq94 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ X3) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2.2 in 12
  have eq128 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (((X1 ◇ X0) ◇ X1) ◇ (sK1 ◇ X0)) := superpose eq13 eq19 -- superposition 19,13, 13 into 19, unify on (0).2 in 13 and (0).2.1 in 19
  have eq2737 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X3)) = ((X5 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0)) ◇ X5) := superpose eq36 eq94 -- superposition 94,36, 36 into 94, unify on (0).2 in 36 and (0).2 in 94
  have eq3939 (X0 X1 X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0)) ◇ X3) := superpose eq94 eq128 -- superposition 128,94, 94 into 128, unify on (0).2 in 94 and (0).2 in 128
  subsumption eq3939 eq2737


@[equational_result]
theorem Equation4454_implies_Equation4462 (G : Type*) [Magma G] (h : Equation4454 G) : Equation4462 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (X0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq19 (X1 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((X1 ◇ sK2) ◇ X1) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq35 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = (((X2 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2.1 in 9
  have eq94 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ X3) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2.2 in 12
  have eq128 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (((X1 ◇ X0) ◇ X1) ◇ (sK2 ◇ X0)) := superpose eq13 eq19 -- superposition 19,13, 13 into 19, unify on (0).2 in 13 and (0).2.1 in 19
  have eq2737 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X3)) = ((X5 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0)) ◇ X5) := superpose eq35 eq94 -- superposition 94,35, 35 into 94, unify on (0).2 in 35 and (0).2 in 94
  have eq3939 (X0 X1 X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0)) ◇ X3) := superpose eq94 eq128 -- superposition 128,94, 94 into 128, unify on (0).2 in 94 and (0).2 in 128
  subsumption eq3939 eq2737


@[equational_result]
theorem Equation4454_implies_Equation4631 (G : Type*) [Magma G] (h : Equation4454 G) : Equation4631 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK2 ◇ (X0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq24 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq95 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ X3) = (X4 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X2))) := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).2.2.2 in 12
  have eq200 (X1 X2 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ ((X1 ◇ (X2 ◇ X1)) ◇ (sK2 ◇ X1)) := superpose eq15 eq17 -- superposition 17,15, 15 into 17, unify on (0).2 in 15 and (0).2 in 17
  have eq3130 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X3) ◇ X4) = ((X5 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X5) := superpose eq24 eq95 -- superposition 95,24, 24 into 95, unify on (0).2 in 24 and (0).2 in 95
  have eq3315 (X0 X1 X2 X3 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ ((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X3) := superpose eq95 eq200 -- superposition 200,95, 95 into 200, unify on (0).2 in 95 and (0).2 in 200
  subsumption eq3315 eq3130


@[equational_result]
theorem Equation4454_implies_Equation4321 (G : Type*) [Magma G] (h : Equation4454 G) : Equation4321 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = (X1 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq32 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = (((X2 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2.1 in 9
  have eq60 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  have eq72 (X1 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((X1 ◇ sK1) ◇ X1) := superpose eq9 eq60 -- superposition 60,9, 9 into 60, unify on (0).2 in 9 and (0).2 in 60
  have eq73 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X0) = ((X1 ◇ X0) ◇ (X3 ◇ (X4 ◇ X3))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq4155 (X0 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X2)) = ((X0 ◇ (X4 ◇ X0)) ◇ X0) := superpose eq32 eq73 -- superposition 73,32, 32 into 73, unify on (0).2 in 32 and (0).2 in 73
  have eq4291 (X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ (X2 ◇ sK1)) ◇ sK1) := superpose eq73 eq72 -- superposition 72,73, 73 into 72, unify on (0).2 in 73 and (0).2 in 72
  subsumption eq4291 eq4155


@[equational_result]
theorem Equation4454_implies_Equation4389 (G : Type*) [Magma G] (h : Equation4454 G) : Equation4389 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq19 (X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((X1 ◇ sK1) ◇ X1) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq35 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = (((X2 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2.1 in 9
  have eq94 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ X3) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2.2 in 12
  have eq128 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (((X1 ◇ X0) ◇ X1) ◇ (sK1 ◇ X0)) := superpose eq13 eq19 -- superposition 19,13, 13 into 19, unify on (0).2 in 13 and (0).2.1 in 19
  have eq2737 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X3)) = ((X5 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0)) ◇ X5) := superpose eq35 eq94 -- superposition 94,35, 35 into 94, unify on (0).2 in 35 and (0).2 in 94
  have eq3939 (X0 X1 X2 X3 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0)) ◇ X3) := superpose eq94 eq128 -- superposition 128,94, 94 into 128, unify on (0).2 in 94 and (0).2 in 128
  subsumption eq3939 eq2737


@[equational_result]
theorem Equation4454_implies_Equation4392 (G : Type*) [Magma G] (h : Equation4454 G) : Equation4392 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK2 ◇ (X0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq19 (X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((X1 ◇ sK2) ◇ X1) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq36 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = (((X2 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2.1 in 9
  have eq94 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ X3) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2.2 in 12
  have eq128 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (((X1 ◇ X0) ◇ X1) ◇ (sK2 ◇ X0)) := superpose eq13 eq19 -- superposition 19,13, 13 into 19, unify on (0).2 in 13 and (0).2.1 in 19
  have eq2737 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X3)) = ((X5 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0)) ◇ X5) := superpose eq36 eq94 -- superposition 94,36, 36 into 94, unify on (0).2 in 36 and (0).2 in 94
  have eq3939 (X0 X1 X2 X3 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0)) ◇ X3) := superpose eq94 eq128 -- superposition 128,94, 94 into 128, unify on (0).2 in 94 and (0).2 in 128
  subsumption eq3939 eq2737


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
theorem Equation4454_implies_Equation4276 (G : Type*) [Magma G] (h : Equation4454 G) : Equation4276 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = (X1 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq32 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = (((X2 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2.1 in 9
  have eq55 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  have eq72 (X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((X1 ◇ sK1) ◇ X1) := superpose eq9 eq55 -- superposition 55,9, 9 into 55, unify on (0).2 in 9 and (0).2 in 55
  have eq73 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X0) = ((X1 ◇ X0) ◇ (X3 ◇ (X4 ◇ X3))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq4155 (X0 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X2)) = ((X0 ◇ (X4 ◇ X0)) ◇ X0) := superpose eq32 eq73 -- superposition 73,32, 32 into 73, unify on (0).2 in 32 and (0).2 in 73
  have eq4291 (X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ (X2 ◇ sK1)) ◇ sK1) := superpose eq73 eq72 -- superposition 72,73, 73 into 72, unify on (0).2 in 73 and (0).2 in 72
  subsumption eq4291 eq4155


@[equational_result]
theorem Equation3260_implies_Equation3262 (G : Type*) [Magma G] (h : Equation3260 G) : Equation3262 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3260_implies_Equation4341 (G : Type*) [Magma G] (h : Equation3260 G) : Equation4341 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3260_implies_Equation3266 (G : Type*) [Magma G] (h : Equation3260 G) : Equation3266 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


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
theorem Equation854_implies_Equation1022 (G : Type*) [Magma G] (h : Equation854 G) : Equation1022 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq32 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1 in 12
  have eq72 : sK0 ≠ sK0 := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2 in 10
  subsumption eq72 rfl


@[equational_result]
theorem Equation854_implies_Equation4065 (G : Type*) [Magma G] (h : Equation854 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq12 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X4 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))))) = X3 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.2.2.1 in 10
  have eq53 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3)))) = ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3)))) ◇ X0) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).1.2 in 12
  have eq61 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq8 eq53 -- forward demodulation 53,8
  have eq64 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq61 eq9 -- backward demodulation 9,61
  subsumption eq64 eq61


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
theorem Equation854_implies_Equation1028 (G : Type*) [Magma G] (h : Equation854 G) : Equation1028 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq32 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1 in 12
  have eq83 : sK0 ≠ sK0 := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2 in 10
  subsumption eq83 rfl


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
theorem Equation854_implies_Equation1025 (G : Type*) [Magma G] (h : Equation854 G) : Equation1025 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq32 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1 in 12
  have eq83 : sK0 ≠ sK0 := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2 in 10
  subsumption eq83 rfl


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
theorem Equation1460_implies_Equation3519 (G : Type*) [Magma G] (h : Equation1460 G) : Equation3519 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ (X5 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq48 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq48 rfl


@[equational_result]
theorem Equation1460_implies_Equation4357 (G : Type*) [Magma G] (h : Equation1460 G) : Equation4357 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ (X5 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X4 : G) : ((X4 ◇ (X0 ◇ X1)) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).1.1 in 12
  have eq130 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq130 eq26


@[equational_result]
theorem Equation1460_implies_Equation3524 (G : Type*) [Magma G] (h : Equation1460 G) : Equation3524 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ (X5 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq48 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq48 rfl


@[equational_result]
theorem Equation1460_implies_Equation3527 (G : Type*) [Magma G] (h : Equation1460 G) : Equation3527 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ (X5 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq48 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq48 rfl


@[equational_result]
theorem Equation3930_implies_Equation3723 (G : Type*) [Magma G] (h : Equation3930 G) : Equation3723 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ X0) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq17 (X0 X1 X4 : G) : (X4 ◇ (X0 ◇ X1)) = (X4 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq26 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq17 eq9 -- backward demodulation 9,17
  have eq35 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq35 eq26


@[equational_result]
theorem Equation3930_implies_Equation3660 (G : Type*) [Magma G] (h : Equation3930 G) : Equation3660 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ X0) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq17 (X0 X1 X4 : G) : (X4 ◇ (X0 ◇ X1)) = (X4 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq26 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq17 eq9 -- backward demodulation 9,17
  have eq35 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq35 eq26


@[equational_result]
theorem Equation2061_implies_Equation3456 (G : Type*) [Magma G] (h : Equation2061 G) : Equation3456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1.1 in 8
  have eq32 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2 in 11
  have eq60 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq32 eq15 -- superposition 15,32, 32 into 15, unify on (0).2 in 32 and (0).1 in 15
  have eq65 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq10 eq60 -- forward demodulation 60,10
  have eq66 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq8 eq65 -- forward demodulation 65,8
  have eq137 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq66 eq9 -- superposition 9,66, 66 into 9, unify on (0).2 in 66 and (0).2 in 9
  subsumption eq137 rfl


@[equational_result]
theorem Equation2061_implies_Equation3253 (G : Type*) [Magma G] (h : Equation2061 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq32 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2 in 11
  have eq37 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq32 eq9 -- backward demodulation 9,32
  subsumption eq37 eq32


@[equational_result]
theorem Equation2061_implies_Equation255 (G : Type*) [Magma G] (h : Equation2061 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq12 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq14 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1 in 8
  have eq32 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2 in 11
  have eq80 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq32 eq12 -- superposition 12,32, 32 into 12, unify on (0).2 in 32 and (0).1.1.1.2 in 12
  have eq93 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq80 -- forward demodulation 80,12
  have eq94 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq14 eq93 -- forward demodulation 93,14
  have eq95 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq10 eq94 -- forward demodulation 94,10
  have eq106 : sK0 ≠ sK0 := superpose eq95 eq9 -- superposition 9,95, 95 into 9, unify on (0).2 in 95 and (0).2 in 9
  subsumption eq106 rfl


@[equational_result]
theorem Equation2061_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2061 G) : Equation2847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq11 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq10 eq9 -- backward demodulation 9,10
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq13 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq15 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1 in 8
  have eq33 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2 in 12
  have eq91 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq33 eq13 -- superposition 13,33, 33 into 13, unify on (0).2 in 33 and (0).1.1.1.2 in 13
  have eq105 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq13 eq91 -- forward demodulation 91,13
  have eq106 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq15 eq105 -- forward demodulation 105,15
  have eq107 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq10 eq106 -- forward demodulation 106,10
  have eq117 : sK0 ≠ sK0 := superpose eq107 eq11 -- superposition 11,107, 107 into 11, unify on (0).2 in 107 and (0).2 in 11
  subsumption eq117 rfl


@[equational_result]
theorem Equation2061_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2061 G) : Equation2644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq12 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq14 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1 in 8
  have eq32 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2 in 11
  have eq63 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).1.1 in 10
  have eq68 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq10 eq63 -- forward demodulation 63,10
  have eq70 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq68 eq9 -- backward demodulation 9,68
  have eq91 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq32 eq12 -- superposition 12,32, 32 into 12, unify on (0).2 in 32 and (0).1.1.1.2 in 12
  have eq105 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq91 -- forward demodulation 91,12
  have eq106 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq14 eq105 -- forward demodulation 105,14
  have eq107 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq10 eq106 -- forward demodulation 106,10
  have eq117 : sK0 ≠ sK0 := superpose eq107 eq70 -- superposition 70,107, 107 into 70, unify on (0).2 in 107 and (0).2 in 70
  subsumption eq117 rfl


@[equational_result]
theorem Equation2061_implies_Equation307 (G : Type*) [Magma G] (h : Equation2061 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq32 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2 in 11
  have eq58 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq32 eq9 -- superposition 9,32, 32 into 9, unify on (0).2 in 32 and (0).2 in 9
  subsumption eq58 rfl


@[equational_result]
theorem Equation2753_implies_Equation2466 (G : Type*) [Magma G] (h : Equation2753 G) : Equation2466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq19 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq19 eq18


@[equational_result]
theorem Equation2753_implies_Equation2601 (G : Type*) [Magma G] (h : Equation2753 G) : Equation2601 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK2) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq19 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq19 eq18


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
theorem Equation4299_implies_Equation4343 (G : Type*) [Magma G] (h : Equation4299 G) : Equation4343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = (X3 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) = (X3 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq33 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ X1)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq13 eq18 -- superposition 18,13, 13 into 18, unify on (0).2 in 13 and (0).1 in 18
  have eq275 (X0 X1 X3 X4 : G) : (X3 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X4)) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).2 in 15
  have eq308 (X1 X2 : G) : (X2 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1)) := superpose eq15 eq33 -- superposition 33,15, 15 into 33, unify on (0).2 in 15 and (0).1 in 33
  subsumption eq308 eq275


@[equational_result]
theorem Equation4299_implies_Equation4307 (G : Type*) [Magma G] (h : Equation4299 G) : Equation4307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) = (X3 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq74 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK2)) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq17 eq18 -- superposition 18,17, 17 into 18, unify on (0).2 in 17 and (0).1 in 18
  have eq271 (X0 X1 X3 X4 : G) : (X3 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X4)) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).2 in 15
  have eq331 (X1 X2 : G) : (X2 ◇ (sK2 ◇ sK2)) ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1)) := superpose eq15 eq74 -- superposition 74,15, 15 into 74, unify on (0).2 in 15 and (0).2 in 74
  subsumption eq331 eq271


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
theorem Equation4299_implies_Equation4341 (G : Type*) [Magma G] (h : Equation4299 G) : Equation4341 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = (X3 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) = (X3 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq29 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK2)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq75 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK2 ◇ X0)) := superpose eq17 eq29 -- superposition 29,17, 17 into 29, unify on (0).2 in 17 and (0).2 in 29
  have eq269 (X0 X1 X3 X4 : G) : (X3 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X4)) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).2 in 15
  have eq302 (X1 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X1)) := superpose eq15 eq75 -- superposition 75,15, 15 into 75, unify on (0).2 in 15 and (0).2 in 75
  subsumption eq302 eq269


@[equational_result]
theorem Equation4299_implies_Equation4284 (G : Type*) [Magma G] (h : Equation4299 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = (X3 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) = (X3 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq29 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq73 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ X0)) ≠ (X1 ◇ (sK1 ◇ sK1)) := superpose eq17 eq29 -- superposition 29,17, 17 into 29, unify on (0).2 in 17 and (0).1 in 29
  have eq278 (X0 X1 X3 X4 : G) : (X3 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X4)) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).2 in 15
  have eq311 (X1 X2 : G) : (X2 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1)) := superpose eq15 eq73 -- superposition 73,15, 15 into 73, unify on (0).2 in 15 and (0).1 in 73
  subsumption eq311 eq278


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
theorem Equation4299_implies_Equation4293 (G : Type*) [Magma G] (h : Equation4299 G) : Equation4293 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) = (X3 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq74 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq17 eq18 -- superposition 18,17, 17 into 18, unify on (0).2 in 17 and (0).1 in 18
  have eq271 (X0 X1 X3 X4 : G) : (X3 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X4)) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).2 in 15
  have eq331 (X1 X2 : G) : (X2 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1)) := superpose eq15 eq74 -- superposition 74,15, 15 into 74, unify on (0).2 in 15 and (0).2 in 74
  subsumption eq331 eq271


@[equational_result]
theorem Equation4299_implies_Equation4276 (G : Type*) [Magma G] (h : Equation4299 G) : Equation4276 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) = (X3 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq9 eq18 -- superposition 18,9, 9 into 18, unify on (0).2 in 9 and (0).1 in 18
  have eq324 (X0 X1 X3 X4 : G) : (X3 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X4)) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).2 in 15
  have eq357 (X1 X2 : G) : (X2 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1)) := superpose eq15 eq21 -- superposition 21,15, 15 into 21, unify on (0).2 in 15 and (0).2 in 21
  subsumption eq357 eq324


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
theorem Equation2227_implies_Equation3887 (G : Type*) [Magma G] (h : Equation2227 G) : Equation3887 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X3 ◇ X4) ◇ (X4 ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X3 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq42 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq42 rfl


@[equational_result]
theorem Equation2227_implies_Equation3935 (G : Type*) [Magma G] (h : Equation2227 G) : Equation3935 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X3 ◇ X4) ◇ (X4 ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X3 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq42 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq42 rfl


@[equational_result]
theorem Equation2227_implies_Equation4606 (G : Type*) [Magma G] (h : Equation2227 G) : Equation4606 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X3 ◇ X4) ◇ (X4 ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X2 X3 X4 : G) : (X3 ◇ ((X2 ◇ X3) ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq26 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq120 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq120 eq26


@[equational_result]
theorem Equation2227_implies_Equation4689 (G : Type*) [Magma G] (h : Equation2227 G) : Equation4689 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK3 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X3 ◇ X4) ◇ (X4 ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X2 X3 X4 : G) : (X3 ◇ ((X2 ◇ X3) ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq26 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq120 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ ((X0 ◇ sK1) ◇ sK2) := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq120 eq26


@[equational_result]
theorem Equation2227_implies_Equation3897 (G : Type*) [Magma G] (h : Equation2227 G) : Equation3897 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X3 ◇ X4) ◇ (X4 ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X3 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq42 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq42 rfl


@[equational_result]
theorem Equation4086_implies_Equation4096 (G : Type*) [Magma G] (h : Equation4086 G) : Equation4096 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X2 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ ((sK2 ◇ sK2) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation4086_implies_Equation4090 (G : Type*) [Magma G] (h : Equation4086 G) : Equation4090 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation4086_implies_Equation4093 (G : Type*) [Magma G] (h : Equation4086 G) : Equation4093 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation2883_implies_Equation4314 (G : Type*) [Magma G] (h : Equation2883 G) : Equation4314 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ X3) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) = ((X0 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X0 X3 X4 : G) : (((X3 ◇ X4) ◇ X3) ◇ ((X4 ◇ X0) ◇ X4)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1.2 in 11
  have eq19 (X0 X1 X4 : G) : (((X4 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X4) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X4 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.1 in 9
  have eq27 (X0 X1 X4 : G) : ((X4 ◇ X0) ◇ X4) = ((X4 ◇ ((X4 ◇ X0) ◇ X4)) ◇ (X0 ◇ X1)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.2 in 12
  have eq35 (X0 X1 X2 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq94 (X0 X1 X3 X4 : G) : ((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X4)) ◇ X3) = ((X3 ◇ ((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X4)) ◇ X3)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq27 eq12 -- superposition 12,27, 27 into 12, unify on (0).2 in 27 and (0).1.1.2.1 in 12
  have eq124 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq19 eq16 -- superposition 16,19, 19 into 16, unify on (0).2 in 19 and (0).1.1 in 16
  have eq334 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq35 eq9 -- superposition 9,35, 35 into 9, unify on (0).2 in 35 and (0).1.1 in 9
  have eq414 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X2) ◇ X0)) ◇ (X1 ◇ (X3 ◇ X4))) := superpose eq124 eq21 -- superposition 21,124, 124 into 21, unify on (0).2 in 124 and (0).2.1 in 21
  have eq499 (X0 X1 X3 X4 : G) : ((X3 ◇ X0) ◇ X3) = ((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X4)) ◇ X3) := superpose eq414 eq94 -- backward demodulation 94,414
  have eq1750 (X0 X1 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X4)) := superpose eq11 eq334 -- superposition 334,11, 11 into 334, unify on (0).2 in 11 and (0).2.2.1 in 334
  have eq2717 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3))) ◇ ((X0 ◇ (X4 ◇ X5)) ◇ X0)) := superpose eq499 eq11 -- superposition 11,499, 499 into 11, unify on (0).2 in 499 and (0).1.1.1 in 11
  have eq2799 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X4 ◇ X5)) ◇ X0)) := superpose eq1750 eq2717 -- forward demodulation 2717,1750
  have eq2800 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) := superpose eq11 eq2799 -- forward demodulation 2799,11
  have eq3261 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = (X2 ◇ (X0 ◇ X3)) := superpose eq19 eq2800 -- superposition 2800,19, 19 into 2800, unify on (0).2 in 19 and (0).2.2.1 in 2800
  have eq4729 (X0 X1 X3 X4 : G) : (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ X4)) := superpose eq3261 eq3261 -- superposition 3261,3261, 3261 into 3261, unify on (0).2 in 3261 and (0).1 in 3261
  have eq6216 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq4729 eq10 -- superposition 10,4729, 4729 into 10, unify on (0).2 in 4729 and (0).2 in 10
  subsumption eq6216 eq4729


@[equational_result]
theorem Equation2883_implies_Equation4357 (G : Type*) [Magma G] (h : Equation2883 G) : Equation4357 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ X3) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) = ((X0 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X0 X3 X4 : G) : (((X3 ◇ X4) ◇ X3) ◇ ((X4 ◇ X0) ◇ X4)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1.2 in 11
  have eq19 (X0 X1 X4 : G) : (((X4 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X4) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X4 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.1 in 9
  have eq27 (X0 X1 X4 : G) : ((X4 ◇ X0) ◇ X4) = ((X4 ◇ ((X4 ◇ X0) ◇ X4)) ◇ (X0 ◇ X1)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.2 in 12
  have eq35 (X0 X1 X2 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq94 (X0 X1 X3 X4 : G) : ((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X4)) ◇ X3) = ((X3 ◇ ((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X4)) ◇ X3)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq27 eq12 -- superposition 12,27, 27 into 12, unify on (0).2 in 27 and (0).1.1.2.1 in 12
  have eq124 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq19 eq16 -- superposition 16,19, 19 into 16, unify on (0).2 in 19 and (0).1.1 in 16
  have eq334 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq35 eq9 -- superposition 9,35, 35 into 9, unify on (0).2 in 35 and (0).1.1 in 9
  have eq414 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X2) ◇ X0)) ◇ (X1 ◇ (X3 ◇ X4))) := superpose eq124 eq21 -- superposition 21,124, 124 into 21, unify on (0).2 in 124 and (0).2.1 in 21
  have eq499 (X0 X1 X3 X4 : G) : ((X3 ◇ X0) ◇ X3) = ((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X4)) ◇ X3) := superpose eq414 eq94 -- backward demodulation 94,414
  have eq1750 (X0 X1 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X4)) := superpose eq11 eq334 -- superposition 334,11, 11 into 334, unify on (0).2 in 11 and (0).2.2.1 in 334
  have eq2717 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3))) ◇ ((X0 ◇ (X4 ◇ X5)) ◇ X0)) := superpose eq499 eq11 -- superposition 11,499, 499 into 11, unify on (0).2 in 499 and (0).1.1.1 in 11
  have eq2799 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X4 ◇ X5)) ◇ X0)) := superpose eq1750 eq2717 -- forward demodulation 2717,1750
  have eq2800 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) := superpose eq11 eq2799 -- forward demodulation 2799,11
  have eq3261 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = (X2 ◇ (X0 ◇ X3)) := superpose eq19 eq2800 -- superposition 2800,19, 19 into 2800, unify on (0).2 in 19 and (0).2.2.1 in 2800
  have eq4729 (X0 X1 X3 X4 : G) : (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ X4)) := superpose eq3261 eq3261 -- superposition 3261,3261, 3261 into 3261, unify on (0).2 in 3261 and (0).1 in 3261
  have eq6216 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq4729 eq10 -- superposition 10,4729, 4729 into 10, unify on (0).2 in 4729 and (0).2 in 10
  subsumption eq6216 eq4729


@[equational_result]
theorem Equation3283_implies_Equation3272 (G : Type*) [Magma G] (h : Equation3283 G) : Equation3272 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq47 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2 in 10
  subsumption eq47 eq14


@[equational_result]
theorem Equation3283_implies_Equation3258 (G : Type*) [Magma G] (h : Equation3283 G) : Equation3258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq47 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2 in 10
  subsumption eq47 eq14


@[equational_result]
theorem Equation3283_implies_Equation4276 (G : Type*) [Magma G] (h : Equation3283 G) : Equation4276 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq47 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq47 eq14


@[equational_result]
theorem Equation3283_implies_Equation3668 (G : Type*) [Magma G] (h : Equation3283 G) : Equation3668 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq24 eq14


@[equational_result]
theorem Equation3283_implies_Equation4343 (G : Type*) [Magma G] (h : Equation3283 G) : Equation4343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq47 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq47 eq14


@[equational_result]
theorem Equation3283_implies_Equation3709 (G : Type*) [Magma G] (h : Equation3283 G) : Equation3709 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq24 eq14


@[equational_result]
theorem Equation3283_implies_Equation3268 (G : Type*) [Magma G] (h : Equation3283 G) : Equation3268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq47 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2 in 10
  subsumption eq47 eq14


@[equational_result]
theorem Equation3283_implies_Equation3262 (G : Type*) [Magma G] (h : Equation3283 G) : Equation3262 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq47 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2 in 10
  subsumption eq47 eq14


@[equational_result]
theorem Equation3283_implies_Equation3266 (G : Type*) [Magma G] (h : Equation3283 G) : Equation3266 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq52 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2 in 10
  subsumption eq52 eq14


@[equational_result]
theorem Equation3283_implies_Equation4351 (G : Type*) [Magma G] (h : Equation3283 G) : Equation4351 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq47 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq47 eq14


@[equational_result]
theorem Equation3283_implies_Equation3288 (G : Type*) [Magma G] (h : Equation3283 G) : Equation3288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq52 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2 in 10
  subsumption eq52 eq14


@[equational_result]
theorem Equation3283_implies_Equation312 (G : Type*) [Magma G] (h : Equation3283 G) : Equation312 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq22 (X0 : G) : (X0 ◇ X0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).1 in 10
  subsumption eq22 eq14


@[equational_result]
theorem Equation3283_implies_Equation4355 (G : Type*) [Magma G] (h : Equation3283 G) : Equation4355 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq47 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq47 eq14


@[equational_result]
theorem Equation3283_implies_Equation3303 (G : Type*) [Magma G] (h : Equation3283 G) : Equation3303 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3))) := mod_symm nh
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq52 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2 in 10
  subsumption eq52 eq14


@[equational_result]
theorem Equation1340_implies_Equation1171 (G : Type*) [Magma G] (h : Equation1340 G) : Equation1171 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq18 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) ◇ X3) ◇ X3) ◇ X4) = (X1 ◇ X4) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq19 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) ◇ X4) ◇ X4) ◇ X3)) ◇ X5) = (X1 ◇ X5) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq24 (X1 X3 X5 : G) : (X1 ◇ X5) = ((X3 ◇ (X1 ◇ X3)) ◇ X5) := superpose eq18 eq19 -- forward demodulation 19,18
  have eq30 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq24 eq10 -- backward demodulation 10,24
  subsumption eq30 eq17


@[equational_result]
theorem Equation1340_implies_Equation3962 (G : Type*) [Magma G] (h : Equation1340 G) : Equation3962 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq24 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- backward demodulation 10,17
  subsumption eq24 rfl


@[equational_result]
theorem Equation1340_implies_Equation500 (G : Type*) [Magma G] (h : Equation1340 G) : Equation500 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq24 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq17 eq10 -- backward demodulation 10,17
  subsumption eq24 eq17


@[equational_result]
theorem Equation1340_implies_Equation3306 (G : Type*) [Magma G] (h : Equation1340 G) : Equation3306 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq24 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- backward demodulation 10,17
  subsumption eq24 rfl


@[equational_result]
theorem Equation1340_implies_Equation1122 (G : Type*) [Magma G] (h : Equation1340 G) : Equation1122 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq24 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq17 eq10 -- backward demodulation 10,17
  subsumption eq24 eq17


@[equational_result]
theorem Equation1340_implies_Equation4131 (G : Type*) [Magma G] (h : Equation1340 G) : Equation4131 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq51 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (X0 ◇ X2) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.2 in 17
  have eq117 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq51 eq10 -- superposition 10,51, 51 into 10, unify on (0).2 in 51 and (0).2 in 10
  subsumption eq117 rfl


@[equational_result]
theorem Equation1340_implies_Equation1780 (G : Type*) [Magma G] (h : Equation1340 G) : Equation1780 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq54 : sK0 ≠ sK0 := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq54 rfl


@[equational_result]
theorem Equation1340_implies_Equation1038 (G : Type*) [Magma G] (h : Equation1340 G) : Equation1038 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq18 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) ◇ X3) ◇ X3) ◇ X4) = (X1 ◇ X4) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq19 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) ◇ X4) ◇ X4) ◇ X3)) ◇ X5) = (X1 ◇ X5) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq24 (X1 X3 X5 : G) : (X1 ◇ X5) = ((X3 ◇ (X1 ◇ X3)) ◇ X5) := superpose eq18 eq19 -- forward demodulation 19,18
  have eq30 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq24 eq10 -- backward demodulation 10,24
  subsumption eq30 eq17


@[equational_result]
theorem Equation1340_implies_Equation1647 (G : Type*) [Magma G] (h : Equation1340 G) : Equation1647 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq54 : sK0 ≠ sK0 := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq54 rfl


@[equational_result]
theorem Equation1340_implies_Equation3261 (G : Type*) [Magma G] (h : Equation1340 G) : Equation3261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq24 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq17 eq10 -- backward demodulation 10,17
  subsumption eq24 rfl


@[equational_result]
theorem Equation1340_implies_Equation1184 (G : Type*) [Magma G] (h : Equation1340 G) : Equation1184 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq24 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq17 eq10 -- backward demodulation 10,17
  subsumption eq24 eq17


@[equational_result]
theorem Equation1340_implies_Equation4065 (G : Type*) [Magma G] (h : Equation1340 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3)) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq16 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (X0 ◇ X2) := superpose eq8 eq16 -- superposition 16,8, 8 into 16, unify on (0).2 in 8 and (0).1.2 in 16
  have eq116 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq50 eq9 -- superposition 9,50, 50 into 9, unify on (0).2 in 50 and (0).2 in 9
  subsumption eq116 rfl


@[equational_result]
theorem Equation1340_implies_Equation1731 (G : Type*) [Magma G] (h : Equation1340 G) : Equation1731 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq54 : sK0 ≠ sK0 := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq54 rfl


@[equational_result]
theorem Equation2097_implies_Equation8 (G : Type*) [Magma G] (h : Equation2097 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation2097_implies_Equation411 (G : Type*) [Magma G] (h : Equation2097 G) : Equation411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq11


@[equational_result]
theorem Equation2097_implies_Equation3319 (G : Type*) [Magma G] (h : Equation2097 G) : Equation3319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 rfl


@[equational_result]
theorem Equation2097_implies_Equation3862 (G : Type*) [Magma G] (h : Equation2097 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 rfl


@[equational_result]
theorem Equation3145_implies_Equation2554 (G : Type*) [Magma G] (h : Equation3145 G) : Equation2554 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK2) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2 in 13
  subsumption eq17 rfl


@[equational_result]
theorem Equation3145_implies_Equation3197 (G : Type*) [Magma G] (h : Equation3145 G) : Equation3197 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK2) ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2 in 13
  subsumption eq17 rfl


@[equational_result]
theorem Equation3145_implies_Equation3065 (G : Type*) [Magma G] (h : Equation3145 G) : Equation3065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation3145_implies_Equation3458 (G : Type*) [Magma G] (h : Equation3145 G) : Equation3458 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 rfl


@[equational_result]
theorem Equation3145_implies_Equation2263 (G : Type*) [Magma G] (h : Equation3145 G) : Equation2263 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation3145_implies_Equation2462 (G : Type*) [Magma G] (h : Equation3145 G) : Equation2462 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation3145_implies_Equation3068 (G : Type*) [Magma G] (h : Equation3145 G) : Equation3068 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation3145_implies_Equation2736 (G : Type*) [Magma G] (h : Equation3145 G) : Equation2736 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq11


@[equational_result]
theorem Equation3145_implies_Equation2430 (G : Type*) [Magma G] (h : Equation3145 G) : Equation2430 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK3))) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq17 : sK0 ≠ ((sK1 ◇ (sK3 ◇ sK3)) ◇ sK0) := superpose eq16 eq10 -- backward demodulation 10,16
  have eq18 : sK0 ≠ ((sK3 ◇ sK3) ◇ sK0) := superpose eq16 eq17 -- forward demodulation 17,16
  subsumption eq18 eq12


@[equational_result]
theorem Equation3145_implies_Equation2452 (G : Type*) [Magma G] (h : Equation3145 G) : Equation2452 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation3145_implies_Equation3525 (G : Type*) [Magma G] (h : Equation3145 G) : Equation3525 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 rfl


@[equational_result]
theorem Equation3145_implies_Equation2646 (G : Type*) [Magma G] (h : Equation3145 G) : Equation2646 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq11


@[equational_result]
theorem Equation3145_implies_Equation4128 (G : Type*) [Magma G] (h : Equation3145 G) : Equation4128 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 rfl


@[equational_result]
theorem Equation3145_implies_Equation4070 (G : Type*) [Magma G] (h : Equation3145 G) : Equation4070 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 rfl


@[equational_result]
theorem Equation3145_implies_Equation2469 (G : Type*) [Magma G] (h : Equation3145 G) : Equation2469 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation3145_implies_Equation2256 (G : Type*) [Magma G] (h : Equation3145 G) : Equation2256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation3145_implies_Equation1647 (G : Type*) [Magma G] (h : Equation3145 G) : Equation1647 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation3145_implies_Equation4138 (G : Type*) [Magma G] (h : Equation3145 G) : Equation4138 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 rfl


@[equational_result]
theorem Equation3145_implies_Equation3071 (G : Type*) [Magma G] (h : Equation3145 G) : Equation3071 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation3145_implies_Equation2484 (G : Type*) [Magma G] (h : Equation3145 G) : Equation2484 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation3145_implies_Equation2472 (G : Type*) [Magma G] (h : Equation3145 G) : Equation2472 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq11


@[equational_result]
theorem Equation3145_implies_Equation2277 (G : Type*) [Magma G] (h : Equation3145 G) : Equation2277 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation3145_implies_Equation2259 (G : Type*) [Magma G] (h : Equation3145 G) : Equation2259 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation3145_implies_Equation1650 (G : Type*) [Magma G] (h : Equation3145 G) : Equation1650 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation3145_implies_Equation2476 (G : Type*) [Magma G] (h : Equation3145 G) : Equation2476 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation3145_implies_Equation2273 (G : Type*) [Magma G] (h : Equation3145 G) : Equation2273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation3145_implies_Equation2285 (G : Type*) [Magma G] (h : Equation3145 G) : Equation2285 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation3145_implies_Equation2739 (G : Type*) [Magma G] (h : Equation3145 G) : Equation2739 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq11


@[equational_result]
theorem Equation1447_implies_Equation4065 (G : Type*) [Magma G] (h : Equation1447 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq16 rfl


@[equational_result]
theorem Equation1447_implies_Equation4067 (G : Type*) [Magma G] (h : Equation1447 G) : Equation4067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation3885_implies_Equation3875 (G : Type*) [Magma G] (h : Equation3885 G) : Equation3875 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq50 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq50 eq23


@[equational_result]
theorem Equation3885_implies_Equation3871 (G : Type*) [Magma G] (h : Equation3885 G) : Equation3871 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq50 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq50 eq23


@[equational_result]
theorem Equation3885_implies_Equation3897 (G : Type*) [Magma G] (h : Equation3885 G) : Equation3897 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq50 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq50 eq23


@[equational_result]
theorem Equation3885_implies_Equation4622 (G : Type*) [Magma G] (h : Equation3885 G) : Equation4622 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq29 (X0 : G) : (X0 ◇ X0) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq29 eq15


@[equational_result]
theorem Equation3885_implies_Equation4591 (G : Type*) [Magma G] (h : Equation3885 G) : Equation4591 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq33 (X0 : G) : (X0 ◇ X0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq33 eq15


@[equational_result]
theorem Equation3885_implies_Equation3908 (G : Type*) [Magma G] (h : Equation3885 G) : Equation3908 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X2) = ((X3 ◇ (X0 ◇ X4)) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq22 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq48 (X0 X2 X3 X4 : G) : (X2 ◇ X2) = ((X3 ◇ (X0 ◇ X4)) ◇ X4) := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1 in 11
  have eq93 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ (X0 ◇ X0)) ◇ sK3) := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).2.1.2 in 10
  have eq470 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ X4) = ((X5 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X3)) ◇ X0) := superpose eq48 eq48 -- superposition 48,48, 48 into 48, unify on (0).2 in 48 and (0).2.1.2 in 48
  have eq565 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) ◇ sK3) := superpose eq9 eq93 -- superposition 93,9, 9 into 93, unify on (0).2 in 9 and (0).2.1.2 in 93
  subsumption eq565 eq470


@[equational_result]
theorem Equation3885_implies_Equation4098 (G : Type*) [Magma G] (h : Equation3885 G) : Equation4098 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq29 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK2) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq29 eq15


@[equational_result]
theorem Equation3885_implies_Equation4341 (G : Type*) [Magma G] (h : Equation3885 G) : Equation4341 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq22 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq93 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).2.2 in 10
  subsumption eq93 rfl


@[equational_result]
theorem Equation3885_implies_Equation3660 (G : Type*) [Magma G] (h : Equation3885 G) : Equation3660 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq22 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq29 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq29 eq22


@[equational_result]
theorem Equation3885_implies_Equation3902 (G : Type*) [Magma G] (h : Equation3885 G) : Equation3902 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq50 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq50 eq23


@[equational_result]
theorem Equation3885_implies_Equation3895 (G : Type*) [Magma G] (h : Equation3885 G) : Equation3895 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq44 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq44 eq23


@[equational_result]
theorem Equation3885_implies_Equation3912 (G : Type*) [Magma G] (h : Equation3885 G) : Equation3912 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK3) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq50 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq50 eq23


@[equational_result]
theorem Equation3081_implies_Equation3061 (G : Type*) [Magma G] (h : Equation3081 G) : Equation3061 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1.1 in 9
  have eq27 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq35 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq27 eq27 -- superposition 27,27, 27 into 27, unify on (0).2 in 27 and (0).1.1.1 in 27
  have eq149 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = X0 := superpose eq35 eq17 -- superposition 17,35, 35 into 17, unify on (0).2 in 35 and (0).1.1 in 17
  have eq253 : sK0 ≠ sK0 := superpose eq149 eq10 -- superposition 10,149, 149 into 10, unify on (0).2 in 149 and (0).2 in 10
  subsumption eq253 rfl


@[equational_result]
theorem Equation3122_implies_Equation2882 (G : Type*) [Magma G] (h : Equation3122 G) : Equation2882 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq22 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation3122_implies_Equation3065 (G : Type*) [Magma G] (h : Equation3122 G) : Equation3065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation3122_implies_Equation2050 (G : Type*) [Magma G] (h : Equation3122 G) : Equation2050 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq11


@[equational_result]
theorem Equation3122_implies_Equation3139 (G : Type*) [Magma G] (h : Equation3122 G) : Equation3139 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq17 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq35 : sK0 ≠ sK0 := superpose eq17 eq15 -- superposition 15,17, 17 into 15, unify on (0).2 in 17 and (0).2 in 15
  subsumption eq35 rfl


@[equational_result]
theorem Equation3122_implies_Equation1228 (G : Type*) [Magma G] (h : Equation3122 G) : Equation1228 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation3122_implies_Equation3176 (G : Type*) [Magma G] (h : Equation3122 G) : Equation3176 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK2) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq34 : sK0 ≠ sK0 := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq34 rfl


@[equational_result]
theorem Equation3122_implies_Equation4070 (G : Type*) [Magma G] (h : Equation3122 G) : Equation4070 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation3122_implies_Equation2659 (G : Type*) [Magma G] (h : Equation3122 G) : Equation2659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq11


@[equational_result]
theorem Equation3898_implies_Equation3685 (G : Type*) [Magma G] (h : Equation3898 G) : Equation3685 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = ((X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X2)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq16 eq14 -- forward demodulation 14,16
  have eq26 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq127 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq127 eq26


@[equational_result]
theorem Equation3898_implies_Equation3864 (G : Type*) [Magma G] (h : Equation3898 G) : Equation3864 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X2)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq55 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq16 -- superposition 16,27, 27 into 16, unify on (0).2 in 27 and (0).2 in 16
  subsumption eq55 eq27


