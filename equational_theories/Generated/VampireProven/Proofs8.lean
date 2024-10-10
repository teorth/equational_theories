import equational_theories.Superposition
import equational_theories.Equations.All
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation3108_implies_Equation2293 (G : Type*) [Magma G] (h : Equation3108 G) : Equation2293 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq24 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.1 in 12
  have eq33 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq32 eq24 -- backward demodulation 24,32
  subsumption eq33 eq12


@[equational_result]
theorem Equation3108_implies_Equation2300 (G : Type*) [Magma G] (h : Equation3108 G) : Equation2300 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.1 in 12
  have eq32 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq31 eq10 -- backward demodulation 10,31
  have eq33 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq19 eq32 -- forward demodulation 32,19
  subsumption eq33 eq22


@[equational_result]
theorem Equation3108_implies_Equation2303 (G : Type*) [Magma G] (h : Equation3108 G) : Equation2303 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.1 in 12
  have eq33 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq32 eq15 -- backward demodulation 15,32
  subsumption eq33 eq12


@[equational_result]
theorem Equation3108_implies_Equation2330 (G : Type*) [Magma G] (h : Equation3108 G) : Equation2330 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq24 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.1 in 12
  have eq33 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq32 eq24 -- backward demodulation 24,32
  subsumption eq33 eq12


@[equational_result]
theorem Equation3108_implies_Equation2337 (G : Type*) [Magma G] (h : Equation3108 G) : Equation2337 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq24 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq25 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq19 eq24 -- forward demodulation 24,19
  have eq33 : sK0 ≠ sK0 := superpose eq22 eq25 -- superposition 25,22, 22 into 25, unify on (0).2 in 22 and (0).2 in 25
  subsumption eq33 rfl


@[equational_result]
theorem Equation3108_implies_Equation2496 (G : Type*) [Magma G] (h : Equation3108 G) : Equation2496 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.1 in 12
  have eq33 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq32 eq15 -- backward demodulation 15,32
  subsumption eq33 eq12


@[equational_result]
theorem Equation3108_implies_Equation2513 (G : Type*) [Magma G] (h : Equation3108 G) : Equation2513 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK2) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq23 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq32 : sK0 ≠ sK0 := superpose eq23 eq14 -- superposition 14,23, 23 into 14, unify on (0).2 in 23 and (0).2 in 14
  subsumption eq32 rfl


@[equational_result]
theorem Equation3108_implies_Equation2655 (G : Type*) [Magma G] (h : Equation3108 G) : Equation2655 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq12


@[equational_result]
theorem Equation3108_implies_Equation2662 (G : Type*) [Magma G] (h : Equation3108 G) : Equation2662 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq12


@[equational_result]
theorem Equation3108_implies_Equation2736 (G : Type*) [Magma G] (h : Equation3108 G) : Equation2736 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq24 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq24 eq12 -- superposition 12,24, 24 into 12, unify on (0).2 in 24 and (0).1.1 in 12
  have eq33 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq32 eq15 -- backward demodulation 15,32
  subsumption eq33 eq12


@[equational_result]
theorem Equation3108_implies_Equation3309 (G : Type*) [Magma G] (h : Equation3108 G) : Equation3309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq39 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq39 rfl


@[equational_result]
theorem Equation3108_implies_Equation333 (G : Type*) [Magma G] (h : Equation3108 G) : Equation333 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.1 in 12
  have eq46 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq31 eq10 -- superposition 10,31, 31 into 10, unify on (0).2 in 31 and (0).2 in 10
  subsumption eq46 rfl


@[equational_result]
theorem Equation3108_implies_Equation3343 (G : Type*) [Magma G] (h : Equation3108 G) : Equation3343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq24 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.1 in 12
  have eq47 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq24 -- superposition 24,32, 32 into 24, unify on (0).2 in 32 and (0).2 in 24
  subsumption eq47 rfl


@[equational_result]
theorem Equation3108_implies_Equation3346 (G : Type*) [Magma G] (h : Equation3108 G) : Equation3346 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.1 in 12
  have eq47 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq15 -- superposition 15,32, 32 into 15, unify on (0).2 in 32 and (0).2 in 15
  subsumption eq47 rfl


@[equational_result]
theorem Equation3108_implies_Equation3509 (G : Type*) [Magma G] (h : Equation3108 G) : Equation3509 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq39 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq39 rfl


@[equational_result]
theorem Equation3108_implies_Equation3546 (G : Type*) [Magma G] (h : Equation3108 G) : Equation3546 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.1 in 12
  have eq47 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq15 -- superposition 15,32, 32 into 15, unify on (0).2 in 32 and (0).2 in 15
  subsumption eq47 rfl


@[equational_result]
theorem Equation3108_implies_Equation3664 (G : Type*) [Magma G] (h : Equation3108 G) : Equation3664 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq12


@[equational_result]
theorem Equation3108_implies_Equation3712 (G : Type*) [Magma G] (h : Equation3108 G) : Equation3712 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq39 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq39 rfl


@[equational_result]
theorem Equation3108_implies_Equation3759 (G : Type*) [Magma G] (h : Equation3108 G) : Equation3759 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq24 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq24 eq12 -- superposition 12,24, 24 into 12, unify on (0).2 in 24 and (0).1.1 in 12
  have eq44 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq15 -- superposition 15,32, 32 into 15, unify on (0).2 in 32 and (0).2 in 15
  subsumption eq44 rfl


@[equational_result]
theorem Equation3108_implies_Equation3880 (G : Type*) [Magma G] (h : Equation3108 G) : Equation3880 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.1 in 12
  have eq33 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq32 eq15 -- backward demodulation 15,32
  subsumption eq33 eq12


@[equational_result]
theorem Equation3108_implies_Equation4284 (G : Type*) [Magma G] (h : Equation3108 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq39 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq39 rfl


@[equational_result]
theorem Equation3108_implies_Equation4291 (G : Type*) [Magma G] (h : Equation3108 G) : Equation4291 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq24 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.1 in 12
  have eq47 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq24 -- superposition 24,32, 32 into 24, unify on (0).2 in 32 and (0).2 in 24
  subsumption eq47 rfl


@[equational_result]
theorem Equation3108_implies_Equation4320 (G : Type*) [Magma G] (h : Equation3108 G) : Equation4320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK1 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.1 in 12
  have eq47 : (sK1 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq32 eq15 -- superposition 15,32, 32 into 15, unify on (0).2 in 32 and (0).2 in 15
  subsumption eq47 rfl


@[equational_result]
theorem Equation3108_implies_Equation4382 (G : Type*) [Magma G] (h : Equation3108 G) : Equation4382 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq14 -- backward demodulation 14,13
  subsumption eq16 eq13


@[equational_result]
theorem Equation3108_implies_Equation4396 (G : Type*) [Magma G] (h : Equation3108 G) : Equation4396 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq39 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq39 rfl


@[equational_result]
theorem Equation3108_implies_Equation4445 (G : Type*) [Magma G] (h : Equation3108 G) : Equation4445 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK1 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.1 in 12
  have eq47 : (sK1 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq32 eq15 -- superposition 15,32, 32 into 15, unify on (0).2 in 32 and (0).2 in 15
  subsumption eq47 rfl


@[equational_result]
theorem Equation3108_implies_Equation4642 (G : Type*) [Magma G] (h : Equation3108 G) : Equation4642 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK2 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 : sK0 ≠ ((sK2 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq24 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq33 : sK0 ≠ sK0 := superpose eq24 eq14 -- superposition 14,24, 24 into 14, unify on (0).2 in 24 and (0).2 in 14
  subsumption eq33 rfl


@[equational_result]
theorem Equation3108_implies_Equation616 (G : Type*) [Magma G] (h : Equation3108 G) : Equation616 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq14 -- backward demodulation 14,13
  subsumption eq16 eq13


@[equational_result]
theorem Equation3108_implies_Equation822 (G : Type*) [Magma G] (h : Equation3108 G) : Equation822 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq13


@[equational_result]
theorem Equation3109_implies_Equation2924 (G : Type*) [Magma G] (h : Equation3109 G) : Equation2924 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK2)) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq21 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X0 := superpose eq14 eq9 -- backward demodulation 9,14
  have eq22 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq28 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq14 eq21 -- forward demodulation 21,14
  have eq29 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq14 eq28 -- forward demodulation 28,14
  have eq30 : sK0 ≠ (sK1 ◇ sK1) := superpose eq14 eq22 -- forward demodulation 22,14
  subsumption eq30 eq29


@[equational_result]
theorem Equation3113_implies_Equation23 (G : Type*) [Magma G] (h : Equation3113 G) : Equation23 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.1 in 8
  have eq13 (X0 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1.1.2 in 10
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq13 -- forward demodulation 13,8
  have eq21 : sK0 ≠ sK0 := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2 in 9
  subsumption eq21 rfl


@[equational_result]
theorem Equation3114_implies_Equation890 (G : Type*) [Magma G] (h : Equation3114 G) : Equation890 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq17 (X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ X3) = X2 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq18 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0))) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq19 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq12 eq17 -- forward demodulation 17,12
  subsumption eq18 eq19


@[equational_result]
theorem Equation3117_implies_Equation1886 (G : Type*) [Magma G] (h : Equation3117 G) : Equation1886 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2 in 12
  have eq21 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ X1) ◇ X3) = X2 := superpose eq15 eq11 -- backward demodulation 11,15
  have eq37 (X3 X4 : G) : X3 = X4 := superpose eq21 eq21 -- superposition 21,21, 21 into 21, unify on (0).2 in 21 and (0).1 in 21
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq10 -- superposition 10,37, 37 into 10, unify on (0).2 in 37 and (0).2 in 10
  subsumption eq58 eq37


@[equational_result]
theorem Equation3119_implies_Equation3117 (G : Type*) [Magma G] (h : Equation3119 G) : Equation3117 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq15 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq19 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq22 (X1 X2 : G) : X1 = X2 := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1 in 15
  have eq27 (X0 : G) : sK0 ≠ (X0 ◇ sK2) := superpose eq15 eq19 -- superposition 19,15, 15 into 19, unify on (0).2 in 15 and (0).2.1 in 19
  subsumption eq27 eq22


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
theorem Equation3123_implies_Equation1083 (G : Type*) [Magma G] (h : Equation3123 G) : Equation1083 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq18 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq20 (X0 X1 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq15 eq11 -- backward demodulation 11,15
  have eq21 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq15 eq9 -- backward demodulation 9,15
  have eq22 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X0 := superpose eq18 eq20 -- backward demodulation 20,18
  have eq30 (X0 X2 : G) : X0 = X2 := superpose eq21 eq22 -- superposition 22,21, 21 into 22, unify on (0).2 in 21 and (0).1 in 22
  have eq41 (X0 : G) : sK0 ≠ (sK1 ◇ X0) := superpose eq30 eq14 -- superposition 14,30, 30 into 14, unify on (0).2 in 30 and (0).2.2 in 14
  subsumption eq41 eq30


@[equational_result]
theorem Equation3123_implies_Equation507 (G : Type*) [Magma G] (h : Equation3123 G) : Equation507 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq17 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq18 (X0 X1 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq19 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq14 eq9 -- backward demodulation 9,14
  have eq20 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq18 -- backward demodulation 18,17
  have eq24 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK2)) := superpose eq20 eq10 -- backward demodulation 10,20
  have eq29 (X0 X2 : G) : X0 = X2 := superpose eq19 eq20 -- superposition 20,19, 19 into 20, unify on (0).2 in 19 and (0).1 in 20
  have eq33 : sK0 ≠ sK1 := superpose eq20 eq24 -- superposition 24,20, 20 into 24, unify on (0).2 in 20 and (0).2 in 24
  subsumption eq33 eq29


@[equational_result]
theorem Equation3123_implies_Equation685 (G : Type*) [Magma G] (h : Equation3123 G) : Equation685 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK3))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq17 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq18 (X0 X1 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq20 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK2)) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq21 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq18 -- backward demodulation 18,17
  have eq33 : sK0 ≠ sK0 := superpose eq21 eq20 -- superposition 20,21, 21 into 20, unify on (0).2 in 21 and (0).2 in 20
  subsumption eq33 rfl


@[equational_result]
theorem Equation3127_implies_Equation1896 (G : Type*) [Magma G] (h : Equation3127 G) : Equation1896 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq29 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq36 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ ((X0 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := superpose eq29 eq11 -- backward demodulation 11,29
  have eq51 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq29 eq10 -- backward demodulation 10,29
  have eq54 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := superpose eq29 eq36 -- forward demodulation 36,29
  have eq55 (X0 X1 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ X0) = X0 := superpose eq29 eq54 -- forward demodulation 54,29
  have eq56 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ X0) = X0 := superpose eq29 eq55 -- forward demodulation 55,29
  have eq57 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq29 eq56 -- forward demodulation 56,29
  subsumption eq51 eq57


@[equational_result]
theorem Equation3130_implies_Equation2633 (G : Type*) [Magma G] (h : Equation3130 G) : Equation2633 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK3) ◇ sK3)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq13 eq12 -- backward demodulation 12,13
  have eq17 : sK0 ≠ ((sK1 ◇ sK3) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation3135_implies_Equation3228 (G : Type*) [Magma G] (h : Equation3135 G) : Equation3228 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK2) ◇ sK3) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 (X2 X3 : G) : X2 = X3 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1 in 13
  have eq26 (X0 X1 : G) : sK0 ≠ ((X0 ◇ (X1 ◇ X0)) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq26 eq18


@[equational_result]
theorem Equation3141_implies_Equation674 (G : Type*) [Magma G] (h : Equation3141 G) : Equation674 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ X2) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X0 := superpose eq12 eq13 -- forward demodulation 13,12
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq19 (X0 X1 : G) : sK0 ≠ (sK1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2 in 10
  subsumption eq19 eq17


@[equational_result]
theorem Equation3144_implies_Equation1490 (G : Type*) [Magma G] (h : Equation3144 G) : Equation1490 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq19 (X0 X1 : G) : sK0 ≠ ((X0 ◇ X0) ◇ X1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq19 eq17


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
theorem Equation3151_implies_Equation908 (G : Type*) [Magma G] (h : Equation3151 G) : Equation908 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) ◇ X2) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq17 (X1 X3 X4 : G) : ((X1 ◇ X3) ◇ X4) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq26 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq17 eq9 -- backward demodulation 9,17
  have eq27 : sK0 ≠ (sK1 ◇ sK0) := superpose eq17 eq10 -- backward demodulation 10,17
  subsumption eq27 eq26


@[equational_result]
theorem Equation315_implies_Equation3278 (G : Type*) [Magma G] (h : Equation315 G) : Equation3278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq30 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq55 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ (X0 ◇ sK0))) := superpose eq11 eq30 -- superposition 30,11, 11 into 30, unify on (0).2 in 11 and (0).2.2 in 30
  have eq63 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq9 eq55 -- forward demodulation 55,9
  subsumption eq63 eq9


@[equational_result]
theorem Equation3159_implies_Equation2567 (G : Type*) [Magma G] (h : Equation3159 G) : Equation2567 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).1.1.1 in 13
  have eq18 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation3160_implies_Equation2701 (G : Type*) [Magma G] (h : Equation3160 G) : Equation2701 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq19 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq26 (X0 : G) : sK0 ≠ (X0 ◇ sK2) := superpose eq14 eq19 -- superposition 19,14, 14 into 19, unify on (0).2 in 14 and (0).2.1 in 19
  subsumption eq26 eq14


@[equational_result]
theorem Equation3163_implies_Equation2633 (G : Type*) [Magma G] (h : Equation3163 G) : Equation2633 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK3) ◇ sK3)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ ((sK1 ◇ sK3) ◇ sK0) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq16 eq15


@[equational_result]
theorem Equation3176_implies_Equation1238 (G : Type*) [Magma G] (h : Equation3176 G) : Equation1238 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq13 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation3176_implies_Equation270 (G : Type*) [Magma G] (h : Equation3176 G) : Equation270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation3177_implies_Equation1765 (G : Type*) [Magma G] (h : Equation3177 G) : Equation1765 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1.1 in 9
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq19 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ sK0)) := superpose eq18 eq10 -- backward demodulation 10,18
  have eq24 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2))) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq38 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).1.2 in 13
  have eq41 (X0 X2 X3 : G) : (X2 ◇ ((X0 ◇ X3) ◇ X0)) = X0 := superpose eq18 eq24 -- forward demodulation 24,18
  have eq42 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq38 eq16 -- backward demodulation 16,38
  have eq48 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq42 eq41 -- backward demodulation 41,42
  have eq51 : sK0 ≠ ((sK1 ◇ sK2) ◇ sK2) := superpose eq42 eq19 -- backward demodulation 19,42
  subsumption eq51 eq48


@[equational_result]
theorem Equation3181_implies_Equation673 (G : Type*) [Magma G] (h : Equation3181 G) : Equation673 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2 in 12
  have eq19 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq64 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq77 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq64 eq9 -- backward demodulation 9,64
  have eq114 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq64 eq19 -- backward demodulation 19,64
  have eq117 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq77 eq64 -- backward demodulation 64,77
  subsumption eq114 eq117


@[equational_result]
theorem Equation3194_implies_Equation884 (G : Type*) [Magma G] (h : Equation3194 G) : Equation884 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq17 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK1 ◇ sK0) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq20 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq12 eq14 -- superposition 14,12, 12 into 14, unify on (0).2 in 12 and (0).2 in 14
  have eq30 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq20 eq9 -- backward demodulation 9,20
  have eq42 (X2 X3 : G) : X2 = X3 := superpose eq30 eq30 -- superposition 30,30, 30 into 30, unify on (0).2 in 30 and (0).1 in 30
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq18 -- superposition 18,42, 42 into 18, unify on (0).2 in 42 and (0).2 in 18
  subsumption eq56 eq42


@[equational_result]
theorem Equation3196_implies_Equation490 (G : Type*) [Magma G] (h : Equation3196 G) : Equation490 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK3)))) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 (X2 X3 : G) : X2 = X3 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq18 (X0 : G) : sK0 ≠ (sK1 ◇ X0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq18 eq16


@[equational_result]
theorem Equation3210_implies_Equation3159 (G : Type*) [Magma G] (h : Equation3210 G) : Equation3159 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK2) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq16 eq12


@[equational_result]
theorem Equation3254_implies_Equation307 (G : Type*) [Magma G] (h : Equation3254 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.2 in 8
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq12 rfl


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
theorem Equation3273_implies_Equation3295 (G : Type*) [Magma G] (h : Equation3273 G) : Equation3295 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq37 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).2 in 16
  subsumption eq37 eq21


@[equational_result]
theorem Equation3274_implies_Equation3288 (G : Type*) [Magma G] (h : Equation3274 G) : Equation3288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1))) = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq17 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X0) = (X2 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq22 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))) = (X3 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq32 (X0 X2 : G) : (X0 ◇ X0) = ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq18 eq22 -- forward demodulation 22,18
  have eq33 (X1 X2 X3 : G) : (X1 ◇ X1) = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq32 eq16 -- backward demodulation 16,32
  have eq83 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ (sK0 ◇ sK0))) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2.2 in 10
  subsumption eq83 eq33


@[equational_result]
theorem Equation3277_implies_Equation3267 (G : Type*) [Magma G] (h : Equation3277 G) : Equation3267 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq15 (X0 X1 X4 : G) : (X0 ◇ X0) = (X4 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq18 -- superposition 18,28, 28 into 18, unify on (0).2 in 28 and (0).2 in 18
  subsumption eq58 eq28


@[equational_result]
theorem Equation3277_implies_Equation3295 (G : Type*) [Magma G] (h : Equation3277 G) : Equation3295 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) := mod_symm nh
  have eq15 (X0 X1 X4 : G) : (X0 ◇ X0) = (X4 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq51 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq18 -- superposition 18,28, 28 into 18, unify on (0).2 in 28 and (0).2 in 18
  subsumption eq51 eq28


@[equational_result]
theorem Equation3277_implies_Equation3299 (G : Type*) [Magma G] (h : Equation3277 G) : Equation3299 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq15 (X0 X1 X4 : G) : (X0 ◇ X0) = (X4 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq51 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq18 -- superposition 18,28, 28 into 18, unify on (0).2 in 28 and (0).2 in 18
  subsumption eq51 eq28


@[equational_result]
theorem Equation3277_implies_Equation3304 (G : Type*) [Magma G] (h : Equation3277 G) : Equation3304 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK4))) := mod_symm nh
  have eq15 (X0 X1 X4 : G) : (X0 ◇ X0) = (X4 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq18 -- superposition 18,28, 28 into 18, unify on (0).2 in 28 and (0).2 in 18
  subsumption eq58 eq28


@[equational_result]
theorem Equation3280_implies_Equation3257 (G : Type*) [Magma G] (h : Equation3280 G) : Equation3257 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.2 in 9
  have eq37 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq27 -- superposition 27,9, 9 into 27, unify on (0).2 in 9 and (0).2 in 27
  have eq105 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq37 eq16 -- superposition 16,37, 37 into 16, unify on (0).2 in 37 and (0).2 in 16
  subsumption eq105 eq37


@[equational_result]
theorem Equation3280_implies_Equation3283 (G : Type*) [Magma G] (h : Equation3280 G) : Equation3283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.2 in 9
  have eq37 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq27 -- superposition 27,9, 9 into 27, unify on (0).2 in 9 and (0).2 in 27
  have eq105 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq37 eq16 -- superposition 16,37, 37 into 16, unify on (0).2 in 37 and (0).2 in 16
  subsumption eq105 eq37


@[equational_result]
theorem Equation3280_implies_Equation3284 (G : Type*) [Magma G] (h : Equation3280 G) : Equation3284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.2 in 9
  have eq37 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq27 -- superposition 27,9, 9 into 27, unify on (0).2 in 9 and (0).2 in 27
  have eq105 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq37 eq16 -- superposition 16,37, 37 into 16, unify on (0).2 in 37 and (0).2 in 16
  subsumption eq105 eq37


@[equational_result]
theorem Equation3280_implies_Equation3285 (G : Type*) [Magma G] (h : Equation3280 G) : Equation3285 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.2 in 9
  have eq37 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq27 -- superposition 27,9, 9 into 27, unify on (0).2 in 9 and (0).2 in 27
  have eq105 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq37 eq16 -- superposition 16,37, 37 into 16, unify on (0).2 in 37 and (0).2 in 16
  subsumption eq105 eq37


@[equational_result]
theorem Equation3280_implies_Equation3287 (G : Type*) [Magma G] (h : Equation3280 G) : Equation3287 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.2 in 9
  have eq37 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq27 -- superposition 27,9, 9 into 27, unify on (0).2 in 9 and (0).2 in 27
  have eq105 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq37 eq16 -- superposition 16,37, 37 into 16, unify on (0).2 in 37 and (0).2 in 16
  subsumption eq105 eq37


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
theorem Equation3284_implies_Equation3288 (G : Type*) [Magma G] (h : Equation3284 G) : Equation3288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X3 ◇ (X2 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq20 (X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1))) = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1 in 14
  have eq21 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq40 (X1 X2 X3 : G) : (X1 ◇ X1) = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq16 eq20 -- forward demodulation 20,16
  have eq128 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ (sK0 ◇ sK0))) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2.2 in 10
  subsumption eq128 eq40


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
theorem Equation3317_implies_Equation325 (G : Type*) [Magma G] (h : Equation3317 G) : Equation325 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation3324_implies_Equation308 (G : Type*) [Magma G] (h : Equation3324 G) : Equation308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ X0) = (X4 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation3324_implies_Equation327 (G : Type*) [Magma G] (h : Equation3324 G) : Equation327 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ X0) = (X4 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation3324_implies_Equation3527 (G : Type*) [Magma G] (h : Equation3324 G) : Equation3527 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ X0) = (X4 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation3324_implies_Equation4357 (G : Type*) [Magma G] (h : Equation3324 G) : Equation4357 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ X0) = (X4 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq14 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation3344_implies_Equation3806 (G : Type*) [Magma G] (h : Equation3344 G) : Equation3806 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X2 : G) : (X0 ◇ X2) = (X2 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq23 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq32 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq35 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq11 eq23 -- forward demodulation 23,11
  have eq70 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ (X2 ◇ X3))) := superpose eq9 eq32 -- superposition 32,9, 9 into 32, unify on (0).2 in 9 and (0).2 in 32
  have eq85 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq70 -- forward demodulation 70,9
  have eq87 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ X1)) := superpose eq85 eq11 -- backward demodulation 11,85
  have eq99 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq12 eq87 -- superposition 87,12, 12 into 87, unify on (0).2 in 12 and (0).2.2 in 87
  have eq126 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq35 eq10 -- superposition 10,35, 35 into 10, unify on (0).2 in 35 and (0).2 in 10
  subsumption eq126 eq99


@[equational_result]
theorem Equation3347_implies_Equation4195 (G : Type*) [Magma G] (h : Equation3347 G) : Equation4195 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ X0) = (X0 ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq15 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq19 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq15 eq14 -- backward demodulation 14,15
  have eq24 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X0 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq27 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq32 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq41 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).2.2.2 in 9
  have eq42 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).2.2 in 11
  have eq45 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq11 eq42 -- forward demodulation 42,11
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq27 eq45 -- forward demodulation 45,27
  have eq47 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq46 eq10 -- backward demodulation 10,46
  have eq50 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2))) = ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq53 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).1.2 in 19
  have eq56 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq62 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq32 eq53 -- forward demodulation 53,32
  have eq65 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) = ((X0 ◇ X2) ◇ X1) := superpose eq62 eq50 -- backward demodulation 50,62
  have eq66 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq56 eq41 -- backward demodulation 41,56
  have eq69 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2))) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq9 eq27 -- superposition 27,9, 9 into 27, unify on (0).2 in 9 and (0).2.1 in 27
  have eq82 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X1 ◇ X0)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq66 eq69 -- forward demodulation 69,66
  have eq83 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X1 ◇ X0)) = ((X0 ◇ X2) ◇ X1) := superpose eq62 eq82 -- forward demodulation 82,62
  have eq84 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X2) ◇ X1) := superpose eq32 eq83 -- forward demodulation 83,32
  have eq85 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) := superpose eq84 eq65 -- backward demodulation 65,84
  have eq89 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq84 eq66 -- backward demodulation 66,84
  have eq94 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X1)) := superpose eq89 eq9 -- backward demodulation 9,89
  have eq95 (X0 X1 X3 : G) : (X3 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq89 eq11 -- backward demodulation 11,89
  have eq98 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq89 eq85 -- backward demodulation 85,89
  have eq115 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq94 eq94 -- superposition 94,94, 94 into 94, unify on (0).2 in 94 and (0).2.2 in 94
  have eq121 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq94 eq94 -- superposition 94,94, 94 into 94, unify on (0).2 in 94 and (0).2 in 94
  have eq137 (X0 X1 X3 : G) : (X1 ◇ X0) = (X3 ◇ (X1 ◇ X0)) := superpose eq98 eq115 -- forward demodulation 115,98
  have eq169 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK1) := superpose eq121 eq47 -- superposition 47,121, 121 into 47, unify on (0).2 in 121 and (0).1 in 47
  have eq182 (X0 X1 : G) : (X0 ◇ sK0) ≠ (X1 ◇ sK1) := superpose eq121 eq169 -- superposition 169,121, 121 into 169, unify on (0).2 in 121 and (0).1 in 169
  have eq262 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X0) := superpose eq95 eq137 -- superposition 137,95, 95 into 137, unify on (0).2 in 95 and (0).2 in 137
  have eq290 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq137 eq262 -- superposition 262,137, 137 into 262, unify on (0).2 in 137 and (0).1 in 262
  have eq330 (X0 X1 X2 : G) : (X1 ◇ X0) ≠ (X2 ◇ sK1) := superpose eq262 eq182 -- superposition 182,262, 262 into 182, unify on (0).2 in 262 and (0).1 in 182
  subsumption eq330 eq290


@[equational_result]
theorem Equation3348_implies_Equation321 (G : Type*) [Magma G] (h : Equation3348 G) : Equation321 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq27 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq22 eq27 -- forward demodulation 27,22
  have eq36 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK1) := superpose eq28 eq10 -- superposition 10,28, 28 into 10, unify on (0).2 in 28 and (0).2 in 10
  have eq45 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq28 eq22 -- superposition 22,28, 28 into 22, unify on (0).2 in 28 and (0).2 in 22
  have eq79 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq45 eq45 -- superposition 45,45, 45 into 45, unify on (0).2 in 45 and (0).1 in 45
  have eq95 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ X0) := superpose eq45 eq36 -- superposition 36,45, 45 into 36, unify on (0).2 in 45 and (0).2 in 36
  subsumption eq95 eq79


@[equational_result]
theorem Equation3348_implies_Equation335 (G : Type*) [Magma G] (h : Equation3348 G) : Equation335 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq27 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq22 eq27 -- forward demodulation 27,22
  have eq45 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq28 eq22 -- superposition 22,28, 28 into 22, unify on (0).2 in 28 and (0).2 in 22
  have eq46 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).2 in 10
  subsumption eq46 eq45


@[equational_result]
theorem Equation3348_implies_Equation3352 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3352 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq26 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq22 eq10 -- backward demodulation 10,22
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq22 eq28 -- forward demodulation 28,22
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq22 -- superposition 22,29, 29 into 22, unify on (0).2 in 29 and (0).2 in 22
  have eq51 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq22 eq26 -- superposition 26,22, 22 into 26, unify on (0).2 in 22 and (0).2 in 26
  subsumption eq51 eq46


@[equational_result]
theorem Equation3348_implies_Equation3565 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3565 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq35 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq29 eq14 -- superposition 14,29, 29 into 14, unify on (0).2 in 29 and (0).2 in 14
  subsumption eq35 rfl


@[equational_result]
theorem Equation3348_implies_Equation3654 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3654 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK3 ◇ sK4) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK4 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq33 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq29 eq29 -- superposition 29,29, 29 into 29, unify on (0).2 in 29 and (0).2.2 in 29
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq23 -- superposition 23,29, 29 into 23, unify on (0).2 in 29 and (0).2 in 23
  have eq93 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK2) := superpose eq33 eq14 -- superposition 14,33, 33 into 14, unify on (0).2 in 33 and (0).2 in 14
  subsumption eq93 eq46


@[equational_result]
theorem Equation3348_implies_Equation4164 (G : Type*) [Magma G] (h : Equation3348 G) : Equation4164 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq45 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq23 -- superposition 23,29, 29 into 23, unify on (0).2 in 29 and (0).2 in 23
  have eq58 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq45 eq45 -- superposition 45,45, 45 into 45, unify on (0).2 in 45 and (0).1 in 45
  have eq76 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq45 eq14 -- superposition 14,45, 45 into 14, unify on (0).2 in 45 and (0).1 in 14
  subsumption eq76 eq58


@[equational_result]
theorem Equation3348_implies_Equation4178 (G : Type*) [Magma G] (h : Equation3348 G) : Equation4178 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK2) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq21 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq22 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).2 in 15
  have eq26 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq26 eq9 -- backward demodulation 9,26
  have eq59 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq28 eq26 -- superposition 26,28, 28 into 26, unify on (0).2 in 28 and (0).2 in 26
  have eq97 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq59 eq22 -- superposition 22,59, 59 into 22, unify on (0).2 in 59 and (0).2 in 22
  subsumption eq97 rfl


@[equational_result]
theorem Equation3348_implies_Equation4543 (G : Type*) [Magma G] (h : Equation3348 G) : Equation4543 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK0) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK3) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq27 : (sK0 ◇ sK3) ≠ (sK0 ◇ sK2) := superpose eq23 eq14 -- backward demodulation 14,23
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq30 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq29 -- forward demodulation 29,23
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq30 eq23 -- superposition 23,30, 30 into 23, unify on (0).2 in 30 and (0).2 in 23
  have eq79 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq46 eq46 -- superposition 46,46, 46 into 46, unify on (0).2 in 46 and (0).1 in 46
  have eq103 (X0 : G) : (sK0 ◇ sK2) ≠ (X0 ◇ sK0) := superpose eq46 eq27 -- superposition 27,46, 46 into 27, unify on (0).2 in 46 and (0).1 in 27
  subsumption eq103 eq79


@[equational_result]
theorem Equation3349_implies_Equation3388 (G : Type*) [Magma G] (h : Equation3349 G) : Equation3388 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq519 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) := superpose eq486 eq10 -- backward demodulation 10,486
  subsumption eq519 eq301


@[equational_result]
theorem Equation3349_implies_Equation3451 (G : Type*) [Magma G] (h : Equation3349 G) : Equation3451 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq487 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq263 eq348 -- superposition 348,263, 263 into 348, unify on (0).2 in 263 and (0).2 in 348
  have eq515 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK1) := superpose eq348 eq10 -- superposition 10,348, 348 into 10, unify on (0).2 in 348 and (0).2 in 10
  subsumption eq515 eq487


@[equational_result]
theorem Equation335_implies_Equation3456 (G : Type*) [Magma G] (h : Equation335 G) : Equation3456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.2 in 8
  have eq11 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq10 eq9 -- backward demodulation 9,10
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq8 eq11 -- forward demodulation 11,8
  subsumption eq12 eq8


@[equational_result]
theorem Equation335_implies_Equation3659 (G : Type*) [Magma G] (h : Equation335 G) : Equation3659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.2 in 8
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).2.2 in 8
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq8 eq13 -- forward demodulation 13,8
  have eq23 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq8 eq16 -- superposition 16,8, 8 into 16, unify on (0).2 in 8 and (0).2.2 in 16
  have eq40 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq23 eq9 -- superposition 9,23, 23 into 9, unify on (0).2 in 23 and (0).2 in 9
  subsumption eq40 rfl


@[equational_result]
theorem Equation335_implies_Equation3862 (G : Type*) [Magma G] (h : Equation335 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq8 eq9 -- forward demodulation 9,8
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.2 in 8
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 eq8


@[equational_result]
theorem Equation3355_implies_Equation4065 (G : Type*) [Magma G] (h : Equation3355 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.2 in 8
  have eq12 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2 in 12
  have eq18 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq11 eq16 -- forward demodulation 16,11
  subsumption eq18 eq8


@[equational_result]
theorem Equation3358_implies_Equation3548 (G : Type*) [Magma G] (h : Equation3358 G) : Equation3548 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X3 ◇ (X3 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq18 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq24 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq29 (X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X2 ◇ X3)) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq32 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq29 eq14 -- backward demodulation 14,29
  have eq34 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq18 -- forward demodulation 18,13
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq29 eq34 -- forward demodulation 34,29
  have eq42 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq29 eq24 -- forward demodulation 24,29
  have eq43 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ X1) := superpose eq35 eq42 -- forward demodulation 42,35
  have eq47 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq43 eq9 -- backward demodulation 9,43
  have eq52 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq47 eq32 -- superposition 32,47, 47 into 32, unify on (0).2 in 47 and (0).2 in 32
  subsumption eq52 rfl


@[equational_result]
theorem Equation3358_implies_Equation3561 (G : Type*) [Magma G] (h : Equation3358 G) : Equation3561 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X3 ◇ (X3 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq18 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq24 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq29 (X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X2 ◇ X3)) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq30 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ X0) := superpose eq29 eq12 -- backward demodulation 12,29
  have eq32 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq29 eq14 -- backward demodulation 14,29
  have eq34 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq18 -- forward demodulation 18,13
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq29 eq34 -- forward demodulation 34,29
  have eq42 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq29 eq24 -- forward demodulation 24,29
  have eq43 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ X1) := superpose eq35 eq42 -- forward demodulation 42,35
  have eq46 (X0 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X2) ◇ X3) := superpose eq43 eq13 -- backward demodulation 13,43
  have eq47 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq43 eq9 -- backward demodulation 9,43
  have eq55 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq47 eq30 -- superposition 30,47, 47 into 30, unify on (0).2 in 47 and (0).2 in 30
  have eq59 (X0 X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq43 eq55 -- forward demodulation 55,43
  have eq64 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq30 eq46 -- superposition 46,30, 30 into 46, unify on (0).2 in 30 and (0).2 in 46
  have eq91 (X0 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (X0 ◇ sK0)) := superpose eq64 eq32 -- superposition 32,64, 64 into 32, unify on (0).2 in 64 and (0).2.2 in 32
  subsumption eq91 eq59


@[equational_result]
theorem Equation3370_implies_Equation43 (G : Type*) [Magma G] (h : Equation3370 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq21 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq27 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X1)) ◇ X0) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq157 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X2 ◇ (X2 ◇ X3))) := superpose eq9 eq27 -- superposition 27,9, 9 into 27, unify on (0).2 in 9 and (0).2 in 27
  have eq175 (X0 X1 X3 : G) : (X3 ◇ X1) = (X3 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq9 eq157 -- forward demodulation 157,9
  have eq289 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq9 eq175 -- superposition 175,9, 9 into 175, unify on (0).2 in 9 and (0).2 in 175
  have eq500 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq289 eq10 -- superposition 10,289, 289 into 10, unify on (0).2 in 289 and (0).2 in 10
  subsumption eq500 rfl


@[equational_result]
theorem Equation3417_implies_Equation43 (G : Type*) [Magma G] (h : Equation3417 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X1 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq24 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq56 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq9 eq24 -- superposition 24,9, 9 into 24, unify on (0).2 in 9 and (0).2 in 24
  have eq122 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq56 eq10 -- superposition 10,56, 56 into 10, unify on (0).2 in 56 and (0).2 in 10
  subsumption eq122 rfl


@[equational_result]
theorem Equation3473_implies_Equation3499 (G : Type*) [Magma G] (h : Equation3473 G) : Equation3499 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq45 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq20 eq13 -- superposition 13,20, 20 into 13, unify on (0).2 in 20 and (0).2 in 13
  subsumption eq45 eq20


@[equational_result]
theorem Equation3473_implies_Equation3502 (G : Type*) [Magma G] (h : Equation3473 G) : Equation3502 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq45 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq20 eq13 -- superposition 13,20, 20 into 13, unify on (0).2 in 20 and (0).2 in 13
  subsumption eq45 eq20


@[equational_result]
theorem Equation3476_implies_Equation3498 (G : Type*) [Magma G] (h : Equation3476 G) : Equation3498 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK3)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq50 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq50 eq23


@[equational_result]
theorem Equation3477_implies_Equation3499 (G : Type*) [Magma G] (h : Equation3477 G) : Equation3499 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq39 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq39 rfl


@[equational_result]
theorem Equation3478_implies_Equation3504 (G : Type*) [Magma G] (h : Equation3478 G) : Equation3504 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X2) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ ((X1 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq55 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq16 -- superposition 16,27, 27 into 16, unify on (0).2 in 27 and (0).2 in 16
  subsumption eq55 eq27


@[equational_result]
theorem Equation3479_implies_Equation3506 (G : Type*) [Magma G] (h : Equation3479 G) : Equation3506 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X2) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ sK3)) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X3 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq17 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq18 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq18 eq18 -- superposition 18,18, 18 into 18, unify on (0).2 in 18 and (0).2 in 18
  have eq54 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq17 -- superposition 17,27, 27 into 17, unify on (0).2 in 27 and (0).2 in 17
  subsumption eq54 eq27


@[equational_result]
theorem Equation3480_implies_Equation3490 (G : Type*) [Magma G] (h : Equation3480 G) : Equation3490 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X2) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq16 (X0 X2 X5 : G) : (X0 ◇ X0) = (X5 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X3 : G) : (X1 ◇ X1) = (X3 ◇ X3) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq51 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq51 eq27


@[equational_result]
theorem Equation3480_implies_Equation3494 (G : Type*) [Magma G] (h : Equation3480 G) : Equation3494 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X2) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ sK3)) := mod_symm nh
  have eq16 (X0 X2 X5 : G) : (X0 ◇ X0) = (X5 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X3 : G) : (X1 ◇ X1) = (X3 ◇ X3) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3480_implies_Equation3506 (G : Type*) [Magma G] (h : Equation3480 G) : Equation3506 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X2) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ sK3)) := mod_symm nh
  have eq16 (X0 X2 X5 : G) : (X0 ◇ X0) = (X5 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X3 : G) : (X1 ◇ X1) = (X3 ◇ X3) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3483_implies_Equation3460 (G : Type*) [Magma G] (h : Equation3483 G) : Equation3460 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq50 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq50 eq23


@[equational_result]
theorem Equation3483_implies_Equation3487 (G : Type*) [Magma G] (h : Equation3483 G) : Equation3487 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq50 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq50 eq23


@[equational_result]
theorem Equation3483_implies_Equation3488 (G : Type*) [Magma G] (h : Equation3483 G) : Equation3488 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq50 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq50 eq23


@[equational_result]
theorem Equation3483_implies_Equation3489 (G : Type*) [Magma G] (h : Equation3483 G) : Equation3489 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq50 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq50 eq23


@[equational_result]
theorem Equation3483_implies_Equation3490 (G : Type*) [Magma G] (h : Equation3483 G) : Equation3490 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq50 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq50 eq23


@[equational_result]
theorem Equation3486_implies_Equation3473 (G : Type*) [Magma G] (h : Equation3486 G) : Equation3473 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq15 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq22 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).2.2.1 in 9
  have eq25 (X0 : G) : (X0 ◇ X0) ≠ (sK1 ◇ ((X0 ◇ X0) ◇ sK2)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).1 in 10
  subsumption eq25 eq22


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
theorem Equation3492_implies_Equation3504 (G : Type*) [Magma G] (h : Equation3492 G) : Equation3504 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = (X3 ◇ ((X4 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = (X3 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = (X3 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq43 (X0 X1 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ ((X1 ◇ sK3) ◇ X0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq72 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ X3) ◇ (X1 ◇ X1)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2.1 in 15
  have eq111 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X2 ◇ X2)) := superpose eq17 eq15 -- superposition 15,17, 17 into 15, unify on (0).2 in 17 and (0).2.1 in 15
  have eq128 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ X1) := superpose eq111 eq72 -- backward demodulation 72,111
  have eq133 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = ((X3 ◇ ((X4 ◇ X2) ◇ X3)) ◇ (X5 ◇ ((X6 ◇ (X3 ◇ ((X4 ◇ X2) ◇ X3))) ◇ X5))) := superpose eq11 eq14 -- superposition 14,11, 11 into 14, unify on (0).2 in 11 and (0).2.1 in 14
  have eq159 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ ((X2 ◇ (X0 ◇ sK3)) ◇ X1)) ◇ (sK3 ◇ sK3)) := superpose eq14 eq43 -- superposition 43,14, 14 into 43, unify on (0).2 in 14 and (0).2.2 in 43
  have eq170 (X2 X3 X4 X5 X6 : G) : (X2 ◇ X2) = ((X3 ◇ ((X4 ◇ X2) ◇ X3)) ◇ (X5 ◇ ((X6 ◇ (X3 ◇ ((X4 ◇ X2) ◇ X3))) ◇ X5))) := superpose eq17 eq133 -- forward demodulation 133,17
  have eq286 (X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X1)) = (((X2 ◇ X3) ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq339 (X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X1)) = (X1 ◇ X1) := superpose eq128 eq286 -- forward demodulation 286,128
  have eq357 (X2 X3 X5 X6 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ (X5 ◇ ((X6 ◇ (X3 ◇ X3)) ◇ X5))) := superpose eq339 eq170 -- backward demodulation 170,339
  have eq373 (X1 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ X1) ◇ (sK3 ◇ sK3)) := superpose eq339 eq159 -- backward demodulation 159,339
  have eq378 (X2 X3 X5 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ (X5 ◇ X5)) := superpose eq339 eq357 -- forward demodulation 357,339
  subsumption eq373 eq378


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
theorem Equation3494_implies_Equation3503 (G : Type*) [Magma G] (h : Equation3494 G) : Equation3503 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ sK0)) := mod_symm nh
  have eq16 (X1 X3 X5 : G) : (X1 ◇ X1) = (X5 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3494_implies_Equation3507 (G : Type*) [Magma G] (h : Equation3494 G) : Equation3507 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ sK4)) := mod_symm nh
  have eq16 (X1 X3 X5 : G) : (X1 ◇ X1) = (X5 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3495_implies_Equation307 (G : Type*) [Magma G] (h : Equation3495 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X1) ◇ X0)) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.2.1 in 8
  have eq115 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2 in 12
  have eq415 (X2 : G) : (X2 ◇ X2) = (X2 ◇ (X2 ◇ X2)) := superpose eq12 eq115 -- superposition 115,12, 12 into 115, unify on (0).2 in 12 and (0).2.2 in 115
  have eq504 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq415 eq9 -- superposition 9,415, 415 into 9, unify on (0).2 in 415 and (0).2 in 9
  subsumption eq504 rfl


@[equational_result]
theorem Equation3495_implies_Equation3278 (G : Type*) [Magma G] (h : Equation3495 G) : Equation3278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X1) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = (X3 ◇ ((X4 ◇ X3) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X1)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) = (X1 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq165 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = (X3 ◇ (X2 ◇ (X3 ◇ X3))) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).1.2 in 14
  have eq212 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = (X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X0))) := superpose eq11 eq165 -- superposition 165,11, 11 into 165, unify on (0).2 in 11 and (0).2 in 165
  have eq214 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq9 eq165 -- superposition 165,9, 9 into 165, unify on (0).2 in 9 and (0).2 in 165
  have eq257 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ (X2 ◇ X2)) := superpose eq165 eq15 -- superposition 15,165, 165 into 15, unify on (0).2 in 165 and (0).1.1.1 in 15
  have eq310 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = ((X0 ◇ X0) ◇ (X2 ◇ X2)) := superpose eq15 eq257 -- forward demodulation 257,15
  have eq315 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq310 eq214 -- backward demodulation 214,310
  have eq352 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X2) ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq310 eq11 -- superposition 11,310, 310 into 11, unify on (0).2 in 310 and (0).2.2 in 11
  have eq416 (X2 : G) : (X2 ◇ X2) = (X2 ◇ (X2 ◇ X2)) := superpose eq13 eq116 -- superposition 116,13, 13 into 116, unify on (0).2 in 13 and (0).2.2 in 116
  have eq461 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq416 eq315 -- backward demodulation 315,416
  have eq469 (X0 X2 X3 : G) : (X0 ◇ X0) = (X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X0))) := superpose eq461 eq212 -- backward demodulation 212,461
  have eq473 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq469 eq352 -- backward demodulation 352,469
  have eq922 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq473 eq10 -- superposition 10,473, 473 into 10, unify on (0).2 in 473 and (0).2 in 10
  subsumption eq922 rfl


@[equational_result]
theorem Equation3495_implies_Equation3674 (G : Type*) [Magma G] (h : Equation3495 G) : Equation3674 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X1) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X1)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) = (X1 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq165 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = (X3 ◇ (X2 ◇ (X3 ◇ X3))) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).1.2 in 14
  have eq214 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq9 eq165 -- superposition 165,9, 9 into 165, unify on (0).2 in 9 and (0).2 in 165
  have eq257 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ (X2 ◇ X2)) := superpose eq165 eq15 -- superposition 15,165, 165 into 15, unify on (0).2 in 165 and (0).1.1.1 in 15
  have eq310 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = ((X0 ◇ X0) ◇ (X2 ◇ X2)) := superpose eq15 eq257 -- forward demodulation 257,15
  have eq315 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq310 eq214 -- backward demodulation 214,310
  have eq416 (X2 : G) : (X2 ◇ X2) = (X2 ◇ (X2 ◇ X2)) := superpose eq13 eq116 -- superposition 116,13, 13 into 116, unify on (0).2 in 13 and (0).2.2 in 116
  have eq461 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq416 eq315 -- backward demodulation 315,416
  have eq696 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq461 eq10 -- superposition 10,461, 461 into 10, unify on (0).2 in 461 and (0).2 in 10
  subsumption eq696 rfl


@[equational_result]
theorem Equation3498_implies_Equation3502 (G : Type*) [Magma G] (h : Equation3498 G) : Equation3502 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X1) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2.1 in 9
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ ((X0 ◇ X0) ◇ sK3)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2.1 in 10
  subsumption eq26 eq24


@[equational_result]
theorem Equation3501_implies_Equation3466 (G : Type*) [Magma G] (h : Equation3501 G) : Equation3466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X2) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq16 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2.1 in 9
  have eq29 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ ((X0 ◇ X0) ◇ sK2)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2.1 in 10
  subsumption eq29 eq26


@[equational_result]
theorem Equation3501_implies_Equation3486 (G : Type*) [Magma G] (h : Equation3501 G) : Equation3486 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X2) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ ((X0 ◇ X0) ◇ sK2)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2.1 in 10
  have eq53 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X3) = (X4 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0)) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).2.2.1 in 9
  have eq61 (X1 X2 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ sK2)) := superpose eq15 eq26 -- superposition 26,15, 15 into 26, unify on (0).2 in 15 and (0).2.2.1 in 26
  subsumption eq61 eq53


@[equational_result]
theorem Equation3504_implies_Equation3709 (G : Type*) [Magma G] (h : Equation3504 G) : Equation3709 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X3) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq16 (X3 X4 : G) : (X3 ◇ X3) = (X4 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq25 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X0 ◇ X1) ◇ (X2 ◇ X2)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2 in 10
  subsumption eq26 eq25


@[equational_result]
theorem Equation3551_implies_Equation3404 (G : Type*) [Magma G] (h : Equation3551 G) : Equation3404 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ X3) = (X3 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.1 in 11
  have eq14 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (X3 ◇ ((X2 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.1 in 11
  have eq19 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq20 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq11 eq14 -- forward demodulation 14,11
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.2 in 12
  have eq35 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) ◇ X4) = (X4 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2.1 in 11
  have eq42 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq9 eq32 -- forward demodulation 32,9
  have eq45 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ X3) := superpose eq42 eq19 -- backward demodulation 19,42
  have eq49 (X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (X2 ◇ X3) := superpose eq45 eq20 -- backward demodulation 20,45
  have eq55 (X0 X2 : G) : (X0 ◇ X2) = (X2 ◇ (X0 ◇ X0)) := superpose eq42 eq33 -- forward demodulation 33,42
  have eq58 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X4 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (X1 ◇ (X1 ◇ X3)))) := superpose eq42 eq35 -- forward demodulation 35,42
  have eq59 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X4 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0))) := superpose eq45 eq58 -- forward demodulation 58,45
  have eq60 (X0 X1 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X4 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq42 eq59 -- forward demodulation 59,42
  have eq61 (X1 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X1 ◇ X4) := superpose eq45 eq60 -- forward demodulation 60,45
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq42 eq42 -- superposition 42,42, 42 into 42, unify on (0).2 in 42 and (0).2.1 in 42
  have eq102 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ ((X2 ◇ X3) ◇ X2)) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).2 in 42
  have eq121 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq61 eq101 -- forward demodulation 101,61
  have eq124 (X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ X2) ◇ X3) := superpose eq121 eq49 -- backward demodulation 49,121
  have eq125 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq121 eq11 -- backward demodulation 11,121
  have eq128 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK1)) := superpose eq125 eq10 -- backward demodulation 10,125
  have eq129 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq125 eq102 -- forward demodulation 102,125
  have eq130 (X0 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X0)) := superpose eq121 eq129 -- forward demodulation 129,121
  have eq144 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK2) := superpose eq125 eq128 -- superposition 128,125, 125 into 128, unify on (0).2 in 125 and (0).2 in 128
  have eq184 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X2) := superpose eq124 eq121 -- superposition 121,124, 124 into 121, unify on (0).2 in 124 and (0).2 in 121
  have eq224 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK2) := superpose eq184 eq144 -- superposition 144,184, 184 into 144, unify on (0).2 in 184 and (0).2 in 144
  have eq247 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq55 eq130 -- superposition 130,55, 55 into 130, unify on (0).2 in 55 and (0).2 in 130
  have eq276 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X1) := superpose eq184 eq247 -- superposition 247,184, 184 into 247, unify on (0).2 in 184 and (0).1 in 247
  have eq410 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq276 eq276 -- superposition 276,276, 276 into 276, unify on (0).2 in 276 and (0).1 in 276
  have eq447 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X1 ◇ X0) := superpose eq276 eq224 -- superposition 224,276, 276 into 224, unify on (0).2 in 276 and (0).2 in 224
  subsumption eq447 eq410


@[equational_result]
theorem Equation3551_implies_Equation3975 (G : Type*) [Magma G] (h : Equation3551 G) : Equation3975 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ X3) = (X3 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.1 in 11
  have eq14 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (X3 ◇ ((X2 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.1 in 11
  have eq19 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq20 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq11 eq14 -- forward demodulation 14,11
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.2 in 12
  have eq35 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) ◇ X4) = (X4 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2.1 in 11
  have eq42 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq9 eq32 -- forward demodulation 32,9
  have eq45 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ X3) := superpose eq42 eq19 -- backward demodulation 19,42
  have eq49 (X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (X2 ◇ X3) := superpose eq45 eq20 -- backward demodulation 20,45
  have eq55 (X0 X2 : G) : (X0 ◇ X2) = (X2 ◇ (X0 ◇ X0)) := superpose eq42 eq33 -- forward demodulation 33,42
  have eq58 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X4 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (X1 ◇ (X1 ◇ X3)))) := superpose eq42 eq35 -- forward demodulation 35,42
  have eq59 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X4 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0))) := superpose eq45 eq58 -- forward demodulation 58,45
  have eq60 (X0 X1 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X4 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq42 eq59 -- forward demodulation 59,42
  have eq61 (X1 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X1 ◇ X4) := superpose eq45 eq60 -- forward demodulation 60,45
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq42 eq42 -- superposition 42,42, 42 into 42, unify on (0).2 in 42 and (0).2.1 in 42
  have eq102 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ ((X2 ◇ X3) ◇ X2)) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).2 in 42
  have eq121 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq61 eq101 -- forward demodulation 101,61
  have eq124 (X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ X2) ◇ X3) := superpose eq121 eq49 -- backward demodulation 49,121
  have eq125 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq121 eq11 -- backward demodulation 11,121
  have eq128 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq125 eq10 -- backward demodulation 10,125
  have eq129 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq125 eq102 -- forward demodulation 102,125
  have eq130 (X0 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X0)) := superpose eq121 eq129 -- forward demodulation 129,121
  have eq151 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq124 eq128 -- superposition 128,124, 124 into 128, unify on (0).2 in 124 and (0).2 in 128
  have eq249 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq55 eq130 -- superposition 130,55, 55 into 130, unify on (0).2 in 55 and (0).2 in 130
  have eq313 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq249 eq151 -- superposition 151,249, 249 into 151, unify on (0).2 in 249 and (0).2 in 151
  subsumption eq313 rfl


@[equational_result]
theorem Equation3561_implies_Equation3577 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3577 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq126 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK3 ◇ sK0)) := superpose eq108 eq10 -- backward demodulation 10,108
  subsumption eq126 eq116


@[equational_result]
theorem Equation3561_implies_Equation373 (G : Type*) [Magma G] (h : Equation3561 G) : Equation373 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ sK3) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq9 eq29 -- forward demodulation 29,9
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq51 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq51 -- backward demodulation 51,94
  have eq98 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq94 eq24 -- backward demodulation 24,94
  have eq106 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) := superpose eq95 eq35 -- backward demodulation 35,95
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq123 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq108 eq106 -- backward demodulation 106,108
  have eq142 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X2 ◇ (X0 ◇ X4)) := superpose eq116 eq98 -- forward demodulation 98,116
  have eq143 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X4 ◇ X2) := superpose eq116 eq142 -- forward demodulation 142,116
  have eq144 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = (X4 ◇ X2) := superpose eq116 eq143 -- forward demodulation 143,116
  have eq145 (X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X1 ◇ X2) ◇ (X3 ◇ X4)) := superpose eq108 eq144 -- forward demodulation 144,108
  have eq177 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq178 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq177 -- forward demodulation 177,108
  have eq181 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq116 eq178 -- superposition 178,116, 116 into 178, unify on (0).2 in 116 and (0).1 in 178
  have eq194 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK3) := superpose eq181 eq10 -- superposition 10,181, 181 into 10, unify on (0).2 in 181 and (0).2 in 10
  have eq228 (X0 X1 : G) : (X0 ◇ sK0) ≠ (X1 ◇ sK3) := superpose eq181 eq194 -- superposition 194,181, 181 into 194, unify on (0).2 in 181 and (0).1 in 194
  have eq244 (X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ X3) := superpose eq123 eq145 -- superposition 145,123, 123 into 145, unify on (0).2 in 123 and (0).2 in 145
  have eq264 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X1) := superpose eq181 eq244 -- superposition 244,181, 181 into 244, unify on (0).2 in 181 and (0).1 in 244
  have eq397 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq264 eq264 -- superposition 264,264, 264 into 264, unify on (0).2 in 264 and (0).1 in 264
  have eq433 (X0 X1 X2 : G) : (X1 ◇ X0) ≠ (X2 ◇ sK3) := superpose eq264 eq228 -- superposition 228,264, 264 into 228, unify on (0).2 in 264 and (0).1 in 228
  subsumption eq433 eq397


@[equational_result]
theorem Equation3561_implies_Equation384 (G : Type*) [Magma G] (h : Equation3561 G) : Equation384 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq30 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq31 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq9 eq31 -- forward demodulation 31,9
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq30 eq30 -- superposition 30,30, 30 into 30, unify on (0).2 in 30 and (0).2.2 in 30
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq30 eq9 -- superposition 9,30, 30 into 9, unify on (0).2 in 30 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq98 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq94 eq24 -- backward demodulation 24,94
  have eq106 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) := superpose eq95 eq35 -- backward demodulation 35,95
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq123 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq108 eq106 -- backward demodulation 106,108
  have eq126 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq108 eq10 -- backward demodulation 10,108
  have eq143 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X2 ◇ (X0 ◇ X4)) := superpose eq116 eq98 -- forward demodulation 98,116
  have eq144 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X4 ◇ X2) := superpose eq116 eq143 -- forward demodulation 143,116
  have eq145 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = (X4 ◇ X2) := superpose eq116 eq144 -- forward demodulation 144,116
  have eq146 (X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X1 ◇ X2) ◇ (X3 ◇ X4)) := superpose eq108 eq145 -- forward demodulation 145,108
  have eq175 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq176 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq175 -- forward demodulation 175,108
  have eq179 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq116 eq176 -- superposition 176,116, 116 into 176, unify on (0).2 in 116 and (0).1 in 176
  have eq244 (X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ X3) := superpose eq123 eq146 -- superposition 146,123, 123 into 146, unify on (0).2 in 123 and (0).2 in 146
  have eq264 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X1) := superpose eq179 eq244 -- superposition 244,179, 179 into 244, unify on (0).2 in 179 and (0).1 in 244
  have eq354 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq264 eq126 -- superposition 126,264, 264 into 126, unify on (0).2 in 264 and (0).1 in 126
  subsumption eq354 eq264


@[equational_result]
theorem Equation3561_implies_Equation41 (G : Type*) [Magma G] (h : Equation3561 G) : Equation41 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK1 ◇ sK2) ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq9 eq29 -- forward demodulation 29,9
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq98 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq94 eq24 -- backward demodulation 24,94
  have eq106 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) := superpose eq95 eq35 -- backward demodulation 35,95
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq123 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq108 eq106 -- backward demodulation 106,108
  have eq142 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X2 ◇ (X0 ◇ X4)) := superpose eq116 eq98 -- forward demodulation 98,116
  have eq143 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X4 ◇ X2) := superpose eq116 eq142 -- forward demodulation 142,116
  have eq144 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = (X4 ◇ X2) := superpose eq116 eq143 -- forward demodulation 143,116
  have eq145 (X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X1 ◇ X2) ◇ (X3 ◇ X4)) := superpose eq108 eq144 -- forward demodulation 144,108
  have eq177 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq178 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq177 -- forward demodulation 177,108
  have eq181 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq116 eq178 -- superposition 178,116, 116 into 178, unify on (0).2 in 116 and (0).1 in 178
  have eq193 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK2) := superpose eq181 eq10 -- superposition 10,181, 181 into 10, unify on (0).2 in 181 and (0).1 in 10
  have eq226 (X0 X1 : G) : (X0 ◇ sK0) ≠ (X1 ◇ sK2) := superpose eq181 eq193 -- superposition 193,181, 181 into 193, unify on (0).2 in 181 and (0).1 in 193
  have eq242 (X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ X3) := superpose eq123 eq145 -- superposition 145,123, 123 into 145, unify on (0).2 in 123 and (0).2 in 145
  have eq262 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X1) := superpose eq181 eq242 -- superposition 242,181, 181 into 242, unify on (0).2 in 181 and (0).1 in 242
  have eq422 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq262 eq262 -- superposition 262,262, 262 into 262, unify on (0).2 in 262 and (0).1 in 262
  have eq461 (X0 X1 X2 : G) : (X1 ◇ X0) ≠ (X2 ◇ sK2) := superpose eq262 eq226 -- superposition 226,262, 262 into 226, unify on (0).2 in 262 and (0).1 in 226
  subsumption eq461 eq422


@[equational_result]
theorem Equation3565_implies_Equation4212 (G : Type*) [Magma G] (h : Equation3565 G) : Equation4212 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X0) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (X3 ◇ ((X2 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ X4))) = (((X2 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq18 (X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X4))) = ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq24 (X0 X2 X3 X4 : G) : (((X3 ◇ X0) ◇ X0) ◇ X4) = (X4 ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2.2 in 13
  have eq27 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq28 (X0 X2 X3 X4 : G) : (((X3 ◇ X0) ◇ X0) ◇ X4) = (X4 ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.2 in 13
  have eq33 (X1 X2 X3 X4 : G) : (X2 ◇ X4) = (X4 ◇ ((X2 ◇ (X1 ◇ (X1 ◇ X3))) ◇ X2)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2.2.1 in 9
  have eq35 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ X0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq38 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ X4))) = ((X2 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq9 eq15 -- forward demodulation 15,9
  have eq43 (X0 X3 X4 : G) : (((X3 ◇ X0) ◇ X0) ◇ X4) = (X0 ◇ X4) := superpose eq9 eq28 -- forward demodulation 28,9
  have eq44 (X0 X2 X4 : G) : (X4 ◇ (X0 ◇ (X2 ◇ X0))) = (X0 ◇ X4) := superpose eq43 eq24 -- backward demodulation 24,43
  have eq46 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ X3) = (X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X4))) := superpose eq43 eq38 -- backward demodulation 38,43
  have eq47 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ (X2 ◇ X0))) = (X2 ◇ X3) := superpose eq43 eq13 -- backward demodulation 13,43
  have eq48 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ X3) := superpose eq43 eq27 -- backward demodulation 27,43
  have eq51 (X0 X2 X3 X4 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ X3) = (X3 ◇ (X2 ◇ (X2 ◇ X4))) := superpose eq43 eq46 -- forward demodulation 46,43
  have eq54 (X1 X2 X3 : G) : (X1 ◇ X3) = ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) := superpose eq47 eq18 -- backward demodulation 18,47
  have eq56 (X0 X2 X3 : G) : (X2 ◇ X3) = ((X2 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq47 eq51 -- backward demodulation 51,47
  have eq59 (X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X1) ◇ X3) := superpose eq47 eq54 -- forward demodulation 54,47
  have eq61 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ X1) ◇ X3) := superpose eq44 eq48 -- forward demodulation 48,44
  have eq62 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq61 eq9 -- backward demodulation 9,61
  have eq85 (X1 X2 X3 X4 : G) : (X2 ◇ X4) = (X4 ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X2)) := superpose eq61 eq33 -- forward demodulation 33,61
  have eq86 (X1 X2 X4 : G) : (X2 ◇ X4) = (X4 ◇ (X1 ◇ X2)) := superpose eq56 eq85 -- forward demodulation 85,56
  have eq95 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq86 eq35 -- forward demodulation 35,86
  have eq102 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := superpose eq62 eq59 -- superposition 59,62, 62 into 59, unify on (0).2 in 62 and (0).2 in 59
  have eq107 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq62 eq102 -- forward demodulation 102,62
  have eq157 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq107 eq95 -- superposition 95,107, 107 into 95, unify on (0).2 in 107 and (0).2 in 95
  subsumption eq157 rfl


