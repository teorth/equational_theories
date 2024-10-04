import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation2858_implies_Equation2687 (G : Type*) [Magma G] (h : Equation2858 G) : Equation2687 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = ((X0 ◇ X3) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq24 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X4) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq37 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X4) ◇ (X0 ◇ X3)) := superpose eq9 eq24 -- forward demodulation 24,9
  have eq52 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X0 ◇ X3)) := superpose eq9 eq37 -- superposition 37,9, 9 into 37, unify on (0).2 in 9 and (0).2.1 in 37
  have eq69 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X0 := superpose eq52 eq9 -- backward demodulation 9,52
  have eq87 : sK0 ≠ sK0 := superpose eq69 eq10 -- superposition 10,69, 69 into 10, unify on (0).2 in 69 and (0).2 in 10
  subsumption eq87 rfl


@[equational_result]
theorem Equation2858_implies_Equation2679 (G : Type*) [Magma G] (h : Equation2858 G) : Equation2679 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = ((X0 ◇ X3) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq24 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X4) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq37 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X4) ◇ (X0 ◇ X3)) := superpose eq9 eq24 -- forward demodulation 24,9
  have eq52 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X0 ◇ X3)) := superpose eq9 eq37 -- superposition 37,9, 9 into 37, unify on (0).2 in 9 and (0).2.1 in 37
  have eq69 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X0 := superpose eq52 eq9 -- backward demodulation 9,52
  have eq87 : sK0 ≠ sK0 := superpose eq69 eq10 -- superposition 10,69, 69 into 10, unify on (0).2 in 69 and (0).2 in 10
  subsumption eq87 rfl


@[equational_result]
theorem Equation2858_implies_Equation2894 (G : Type*) [Magma G] (h : Equation2858 G) : Equation2894 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK3) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = ((X0 ◇ X3) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq24 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X4) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq37 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X4) ◇ (X0 ◇ X3)) := superpose eq9 eq24 -- forward demodulation 24,9
  have eq52 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X0 ◇ X3)) := superpose eq9 eq37 -- superposition 37,9, 9 into 37, unify on (0).2 in 9 and (0).2.1 in 37
  have eq69 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X0 := superpose eq52 eq9 -- backward demodulation 9,52
  have eq87 : sK0 ≠ sK0 := superpose eq69 eq10 -- superposition 10,69, 69 into 10, unify on (0).2 in 69 and (0).2 in 10
  subsumption eq87 rfl


@[equational_result]
theorem Equation2858_implies_Equation2890 (G : Type*) [Magma G] (h : Equation2858 G) : Equation2890 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = ((X0 ◇ X3) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq24 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X4) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq37 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X4) ◇ (X0 ◇ X3)) := superpose eq9 eq24 -- forward demodulation 24,9
  have eq52 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X0 ◇ X3)) := superpose eq9 eq37 -- superposition 37,9, 9 into 37, unify on (0).2 in 9 and (0).2.1 in 37
  have eq69 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X0 := superpose eq52 eq9 -- backward demodulation 9,52
  have eq87 : sK0 ≠ sK0 := superpose eq69 eq10 -- superposition 10,69, 69 into 10, unify on (0).2 in 69 and (0).2 in 10
  subsumption eq87 rfl


@[equational_result]
theorem Equation2858_implies_Equation2882 (G : Type*) [Magma G] (h : Equation2858 G) : Equation2882 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = ((X0 ◇ X3) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq24 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X4) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq37 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X4) ◇ (X0 ◇ X3)) := superpose eq9 eq24 -- forward demodulation 24,9
  have eq52 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X0 ◇ X3)) := superpose eq9 eq37 -- superposition 37,9, 9 into 37, unify on (0).2 in 9 and (0).2.1 in 37
  have eq69 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X0 := superpose eq52 eq9 -- backward demodulation 9,52
  have eq87 : sK0 ≠ sK0 := superpose eq69 eq10 -- superposition 10,69, 69 into 10, unify on (0).2 in 69 and (0).2 in 10
  subsumption eq87 rfl


@[equational_result]
theorem Equation2858_implies_Equation2646 (G : Type*) [Magma G] (h : Equation2858 G) : Equation2646 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = ((X0 ◇ X3) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq24 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X4) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq37 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X4) ◇ (X0 ◇ X3)) := superpose eq9 eq24 -- forward demodulation 24,9
  have eq52 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X0 ◇ X3)) := superpose eq9 eq37 -- superposition 37,9, 9 into 37, unify on (0).2 in 9 and (0).2.1 in 37
  have eq70 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X0 := superpose eq52 eq9 -- backward demodulation 9,52
  have eq87 : sK0 ≠ sK0 := superpose eq70 eq10 -- superposition 10,70, 70 into 10, unify on (0).2 in 70 and (0).2 in 10
  subsumption eq87 rfl


@[equational_result]
theorem Equation2691_implies_Equation2865 (G : Type*) [Magma G] (h : Equation2691 G) : Equation2865 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (((X4 ◇ X5) ◇ X0) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2691_implies_Equation2886 (G : Type*) [Magma G] (h : Equation2691 G) : Equation2886 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (((X4 ◇ X5) ◇ X0) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2691_implies_Equation2878 (G : Type*) [Magma G] (h : Equation2691 G) : Equation2878 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (((X4 ◇ X5) ◇ X0) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2691_implies_Equation2858 (G : Type*) [Magma G] (h : Equation2691 G) : Equation2858 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (((X4 ◇ X5) ◇ X0) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2691_implies_Equation2875 (G : Type*) [Magma G] (h : Equation2691 G) : Equation2875 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (((X4 ◇ X5) ◇ X0) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2894_implies_Equation266 (G : Type*) [Magma G] (h : Equation2894 G) : Equation266 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (((X4 ◇ X0) ◇ X5) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2894_implies_Equation2691 (G : Type*) [Magma G] (h : Equation2894 G) : Equation2691 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK3)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (((X4 ◇ X0) ◇ X5) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2894_implies_Equation323 (G : Type*) [Magma G] (h : Equation2894 G) : Equation323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (((X4 ◇ X0) ◇ X5) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq36 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq36 rfl


@[equational_result]
theorem Equation2894_implies_Equation2683 (G : Type*) [Magma G] (h : Equation2894 G) : Equation2683 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (((X4 ◇ X0) ◇ X5) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation2894_implies_Equation2665 (G : Type*) [Magma G] (h : Equation2894 G) : Equation2665 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (((X4 ◇ X0) ◇ X5) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2894_implies_Equation2675 (G : Type*) [Magma G] (h : Equation2894 G) : Equation2675 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (((X4 ◇ X0) ◇ X5) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2894_implies_Equation2655 (G : Type*) [Magma G] (h : Equation2894 G) : Equation2655 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (((X4 ◇ X0) ◇ X5) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2065_implies_Equation2676 (G : Type*) [Magma G] (h : Equation2065 G) : Equation2676 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X3 : G) : (((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq19 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq48 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1 in 9
  have eq72 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X5)) = (((((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq101 (X0 X1 X2 : G) : ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) = X0 := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).1.1.1 in 12
  have eq163 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) = ((((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X5)) := superpose eq13 eq48 -- superposition 48,13, 13 into 48, unify on (0).2 in 13 and (0).1 in 48
  have eq264 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2.1 in 17
  have eq290 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X3)) = ((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1.1.1 in 19
  have eq305 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X1 ◇ X5)) := superpose eq264 eq163 -- backward demodulation 163,264
  have eq312 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) := superpose eq9 eq305 -- forward demodulation 305,9
  have eq321 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (((((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq312 eq72 -- backward demodulation 72,312
  have eq357 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) := superpose eq312 eq290 -- forward demodulation 290,312
  have eq358 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq357 eq321 -- backward demodulation 321,357
  have eq362 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1) = X0 := superpose eq358 eq101 -- backward demodulation 101,358
  have eq399 : sK0 ≠ sK0 := superpose eq362 eq10 -- superposition 10,362, 362 into 10, unify on (0).2 in 362 and (0).2 in 10
  subsumption eq399 rfl


@[equational_result]
theorem Equation2065_implies_Equation4282 (G : Type*) [Magma G] (h : Equation2065 G) : Equation4282 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq19 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq48 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1 in 9
  have eq183 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq48 eq10 -- superposition 10,48, 48 into 10, unify on (0).2 in 48 and (0).2 in 10
  subsumption eq183 eq48


@[equational_result]
theorem Equation2065_implies_Equation4357 (G : Type*) [Magma G] (h : Equation2065 G) : Equation4357 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq19 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq48 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1 in 9
  have eq207 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq48 eq10 -- superposition 10,48, 48 into 10, unify on (0).2 in 48 and (0).2 in 10
  subsumption eq207 eq48


@[equational_result]
theorem Equation2065_implies_Equation2866 (G : Type*) [Magma G] (h : Equation2065 G) : Equation2866 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq19 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq51 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq51 rfl


@[equational_result]
theorem Equation2065_implies_Equation2670 (G : Type*) [Magma G] (h : Equation2065 G) : Equation2670 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X3 : G) : (((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq19 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq48 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1 in 9
  have eq72 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X5)) = (((((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq101 (X0 X1 X2 : G) : ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) = X0 := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).1.1.1 in 12
  have eq163 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) = ((((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X5)) := superpose eq13 eq48 -- superposition 48,13, 13 into 48, unify on (0).2 in 13 and (0).1 in 48
  have eq264 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2.1 in 17
  have eq290 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X3)) = ((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1.1.1 in 19
  have eq305 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X1 ◇ X5)) := superpose eq264 eq163 -- backward demodulation 163,264
  have eq312 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) := superpose eq9 eq305 -- forward demodulation 305,9
  have eq321 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (((((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq312 eq72 -- backward demodulation 72,312
  have eq357 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) := superpose eq312 eq290 -- forward demodulation 290,312
  have eq358 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq357 eq321 -- backward demodulation 321,357
  have eq362 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1) = X0 := superpose eq358 eq101 -- backward demodulation 101,358
  have eq399 : sK0 ≠ sK0 := superpose eq362 eq10 -- superposition 10,362, 362 into 10, unify on (0).2 in 362 and (0).2 in 10
  subsumption eq399 rfl


@[equational_result]
theorem Equation2065_implies_Equation2852 (G : Type*) [Magma G] (h : Equation2065 G) : Equation2852 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq19 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq51 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq51 rfl


@[equational_result]
theorem Equation2676_implies_Equation2887 (G : Type*) [Magma G] (h : Equation2676 G) : Equation2887 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = ((X0 ◇ (X1 ◇ X3)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq31 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) ◇ sK1) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2.1 in 10
  subsumption eq31 eq9


@[equational_result]
theorem Equation2676_implies_Equation2063 (G : Type*) [Magma G] (h : Equation2676 G) : Equation2063 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = ((X0 ◇ (X1 ◇ X3)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq26 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X3)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq82 : sK0 ≠ sK0 := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq82 rfl


@[equational_result]
theorem Equation2676_implies_Equation4314 (G : Type*) [Magma G] (h : Equation2676 G) : Equation4314 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = ((X0 ◇ (X1 ◇ X3)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq26 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X3)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq76 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = ((((X0 ◇ X1) ◇ (X1 ◇ X3)) ◇ X1) ◇ (X1 ◇ X4)) := superpose eq11 eq26 -- superposition 26,11, 11 into 26, unify on (0).2 in 11 and (0).1.1.1 in 26
  have eq102 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X4)) := superpose eq9 eq76 -- forward demodulation 76,9
  have eq189 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq102 eq10 -- superposition 10,102, 102 into 10, unify on (0).2 in 102 and (0).2 in 10
  subsumption eq189 eq102


@[equational_result]
theorem Equation2676_implies_Equation2036 (G : Type*) [Magma G] (h : Equation2676 G) : Equation2036 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = ((X0 ◇ (X1 ◇ X3)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq26 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X3)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq82 : sK0 ≠ sK0 := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq82 rfl


@[equational_result]
theorem Equation2887_implies_Equation2065 (G : Type*) [Magma G] (h : Equation2887 G) : Equation2065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq20 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq54 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq54 rfl


@[equational_result]
theorem Equation2887_implies_Equation2646 (G : Type*) [Magma G] (h : Equation2887 G) : Equation2646 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X0) ◇ X0) = ((X4 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.2 in 12
  have eq16 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) ◇ X1) ◇ X1) = (((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq19 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq20 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq30 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ X5) ◇ ((X5 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) ◇ ((X5 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) = X4 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.2.1.2 in 11
  have eq40 (X0 X4 X5 : G) : (((X4 ◇ X5) ◇ ((X5 ◇ X0) ◇ X0)) ◇ ((X5 ◇ X0) ◇ X0)) = X4 := superpose eq14 eq30 -- forward demodulation 30,14
  have eq49 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq55 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.1.2 in 12
  have eq69 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X1 ◇ X2)) := superpose eq55 eq16 -- backward demodulation 16,55
  have eq72 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X1) := superpose eq12 eq69 -- forward demodulation 69,12
  have eq87 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X5)) = (((((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) ◇ X1) ◇ X1) := superpose eq20 eq20 -- superposition 20,20, 20 into 20, unify on (0).2 in 20 and (0).1 in 20
  have eq89 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) := superpose eq9 eq20 -- superposition 20,9, 9 into 20, unify on (0).2 in 9 and (0).2.1.1.1 in 20
  have eq151 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X5)) = (((((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X1 ◇ X2)) ◇ (((X1 ◇ X2) ◇ X3) ◇ X3)) ◇ X1) ◇ X1) ◇ X1) ◇ X1) := superpose eq55 eq87 -- forward demodulation 87,55
  have eq152 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X5)) = (((((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ X1) := superpose eq72 eq151 -- forward demodulation 151,72
  have eq153 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X5)) = ((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) ◇ X1) := superpose eq9 eq152 -- forward demodulation 152,9
  have eq223 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) = ((((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X5)) := superpose eq20 eq49 -- superposition 49,20, 20 into 49, unify on (0).2 in 20 and (0).1 in 49
  have eq298 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) = ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X1 ◇ X5)) := superpose eq55 eq223 -- forward demodulation 223,55
  have eq299 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X1 ◇ X5)) := superpose eq89 eq298 -- forward demodulation 298,89
  have eq300 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) := superpose eq19 eq299 -- forward demodulation 299,19
  have eq309 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) ◇ X1) := superpose eq300 eq153 -- backward demodulation 153,300
  have eq377 (X0 X1 X2 : G) : ((((((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) ◇ X1) ◇ X1) ◇ X1) = X0 := superpose eq20 eq40 -- superposition 40,20, 20 into 40, unify on (0).2 in 20 and (0).1 in 40
  have eq417 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1) = X0 := superpose eq309 eq377 -- forward demodulation 377,309
  have eq461 : sK0 ≠ sK0 := superpose eq417 eq10 -- superposition 10,417, 417 into 10, unify on (0).2 in 417 and (0).2 in 10
  subsumption eq461 rfl


@[equational_result]
theorem Equation2656_implies_Equation2055 (G : Type*) [Magma G] (h : Equation2656 G) : Equation2055 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq19 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X4))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.1 in 11
  have eq25 (X0 X3 X4 : G) : (((X3 ◇ X3) ◇ X4) ◇ ((X4 ◇ X4) ◇ X0)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq101 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2)) = X1 := superpose eq25 eq25 -- superposition 25,25, 25 into 25, unify on (0).2 in 25 and (0).1.2.1 in 25
  have eq116 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq25 eq9 -- superposition 9,25, 25 into 9, unify on (0).2 in 25 and (0).1.1.1 in 9
  have eq398 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) = X0 := superpose eq116 eq15 -- superposition 15,116, 116 into 15, unify on (0).2 in 116 and (0).1.1 in 15
  have eq477 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.1 in 19
  have eq555 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq12 eq477 -- forward demodulation 477,12
  have eq818 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq9 eq398 -- superposition 398,9, 9 into 398, unify on (0).2 in 9 and (0).1.1.1 in 398
  have eq859 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq555 eq818 -- forward demodulation 818,555
  have eq860 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) = X1 := superpose eq859 eq101 -- backward demodulation 101,859
  have eq1183 : sK0 ≠ sK0 := superpose eq860 eq10 -- superposition 10,860, 860 into 10, unify on (0).2 in 860 and (0).2 in 10
  subsumption eq1183 rfl


@[equational_result]
theorem Equation2656_implies_Equation3460 (G : Type*) [Magma G] (h : Equation2656 G) : Equation3460 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq15 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X3)) ◇ X2) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq19 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X4))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.1 in 11
  have eq25 (X0 X3 X4 : G) : (((X3 ◇ X3) ◇ X4) ◇ ((X4 ◇ X4) ◇ X0)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq12 eq31 -- forward demodulation 31,12
  have eq93 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq12 eq25 -- superposition 25,12, 12 into 25, unify on (0).2 in 12 and (0).1.1.1 in 25
  have eq101 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2)) = X1 := superpose eq25 eq25 -- superposition 25,25, 25 into 25, unify on (0).2 in 25 and (0).1.2.1 in 25
  have eq116 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq25 eq9 -- superposition 9,25, 25 into 9, unify on (0).2 in 25 and (0).1.1.1 in 9
  have eq119 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq25 eq13 -- superposition 13,25, 25 into 13, unify on (0).2 in 25 and (0).1 in 13
  have eq173 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq16 eq16 -- superposition 16,16, 16 into 16, unify on (0).2 in 16 and (0).2.1 in 16
  have eq201 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq173 eq41 -- backward demodulation 41,173
  have eq398 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) = X0 := superpose eq116 eq15 -- superposition 15,116, 116 into 15, unify on (0).2 in 116 and (0).1.1 in 15
  have eq417 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := superpose eq116 eq201 -- superposition 201,116, 116 into 201, unify on (0).2 in 116 and (0).2.1.1 in 201
  have eq443 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq93 eq417 -- forward demodulation 417,93
  have eq477 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.1 in 19
  have eq555 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq12 eq477 -- forward demodulation 477,12
  have eq818 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq9 eq398 -- superposition 398,9, 9 into 398, unify on (0).2 in 9 and (0).1.1.1 in 398
  have eq838 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq398 eq398 -- superposition 398,398, 398 into 398, unify on (0).2 in 398 and (0).1.1 in 398
  have eq859 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq555 eq818 -- forward demodulation 818,555
  have eq860 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) = X1 := superpose eq859 eq101 -- backward demodulation 101,859
  have eq872 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq443 eq838 -- forward demodulation 838,443
  have eq1138 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X3)) := superpose eq116 eq860 -- superposition 860,116, 116 into 860, unify on (0).2 in 116 and (0).1.1.1 in 860
  have eq1230 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq119 eq1138 -- forward demodulation 1138,119
  have eq1733 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := superpose eq1230 eq10 -- superposition 10,1230, 1230 into 10, unify on (0).2 in 1230 and (0).2 in 10
  subsumption eq1733 eq872


@[equational_result]
theorem Equation2656_implies_Equation4357 (G : Type*) [Magma G] (h : Equation2656 G) : Equation4357 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq15 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq19 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X4))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.1 in 11
  have eq25 (X0 X3 X4 : G) : (((X3 ◇ X3) ◇ X4) ◇ ((X4 ◇ X4) ◇ X0)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq101 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2)) = X1 := superpose eq25 eq25 -- superposition 25,25, 25 into 25, unify on (0).2 in 25 and (0).1.2.1 in 25
  have eq116 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq25 eq9 -- superposition 9,25, 25 into 9, unify on (0).2 in 25 and (0).1.1.1 in 9
  have eq119 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq25 eq13 -- superposition 13,25, 25 into 13, unify on (0).2 in 25 and (0).1 in 13
  have eq398 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) = X0 := superpose eq116 eq15 -- superposition 15,116, 116 into 15, unify on (0).2 in 116 and (0).1.1 in 15
  have eq477 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.1 in 19
  have eq555 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq12 eq477 -- forward demodulation 477,12
  have eq818 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq9 eq398 -- superposition 398,9, 9 into 398, unify on (0).2 in 9 and (0).1.1.1 in 398
  have eq859 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq555 eq818 -- forward demodulation 818,555
  have eq860 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) = X1 := superpose eq859 eq101 -- backward demodulation 101,859
  have eq1138 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X3)) := superpose eq116 eq860 -- superposition 860,116, 116 into 860, unify on (0).2 in 116 and (0).1.1.1 in 860
  have eq1230 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq119 eq1138 -- forward demodulation 1138,119
  have eq1826 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq1230 eq10 -- superposition 10,1230, 1230 into 10, unify on (0).2 in 1230 and (0).2 in 10
  subsumption eq1826 eq1230


@[equational_result]
theorem Equation2656_implies_Equation3458 (G : Type*) [Magma G] (h : Equation2656 G) : Equation3458 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq15 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X3)) ◇ X2) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq19 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X4))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.1 in 11
  have eq25 (X0 X3 X4 : G) : (((X3 ◇ X3) ◇ X4) ◇ ((X4 ◇ X4) ◇ X0)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq12 eq31 -- forward demodulation 31,12
  have eq93 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq12 eq25 -- superposition 25,12, 12 into 25, unify on (0).2 in 12 and (0).1.1.1 in 25
  have eq101 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2)) = X1 := superpose eq25 eq25 -- superposition 25,25, 25 into 25, unify on (0).2 in 25 and (0).1.2.1 in 25
  have eq116 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq25 eq9 -- superposition 9,25, 25 into 9, unify on (0).2 in 25 and (0).1.1.1 in 9
  have eq119 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq25 eq13 -- superposition 13,25, 25 into 13, unify on (0).2 in 25 and (0).1 in 13
  have eq173 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq16 eq16 -- superposition 16,16, 16 into 16, unify on (0).2 in 16 and (0).2.1 in 16
  have eq201 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq173 eq41 -- backward demodulation 41,173
  have eq398 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) = X0 := superpose eq116 eq15 -- superposition 15,116, 116 into 15, unify on (0).2 in 116 and (0).1.1 in 15
  have eq417 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := superpose eq116 eq201 -- superposition 201,116, 116 into 201, unify on (0).2 in 116 and (0).2.1.1 in 201
  have eq443 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq93 eq417 -- forward demodulation 417,93
  have eq477 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.1 in 19
  have eq555 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq12 eq477 -- forward demodulation 477,12
  have eq818 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq9 eq398 -- superposition 398,9, 9 into 398, unify on (0).2 in 9 and (0).1.1.1 in 398
  have eq838 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq398 eq398 -- superposition 398,398, 398 into 398, unify on (0).2 in 398 and (0).1.1 in 398
  have eq859 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq555 eq818 -- forward demodulation 818,555
  have eq860 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) = X1 := superpose eq859 eq101 -- backward demodulation 101,859
  have eq872 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq443 eq838 -- forward demodulation 838,443
  have eq1138 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X3)) := superpose eq116 eq860 -- superposition 860,116, 116 into 860, unify on (0).2 in 116 and (0).1.1.1 in 860
  have eq1230 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq119 eq1138 -- forward demodulation 1138,119
  have eq1733 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := superpose eq1230 eq10 -- superposition 10,1230, 1230 into 10, unify on (0).2 in 1230 and (0).2 in 10
  subsumption eq1733 eq872


@[equational_result]
theorem Equation2656_implies_Equation3456 (G : Type*) [Magma G] (h : Equation2656 G) : Equation3456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq34 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).1.1 in 11
  have eq55 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq34 eq9 -- superposition 9,34, 34 into 9, unify on (0).2 in 34 and (0).2 in 9
  subsumption eq55 rfl


@[equational_result]
theorem Equation2656_implies_Equation2875 (G : Type*) [Magma G] (h : Equation2656 G) : Equation2875 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq25 (X0 X3 X4 : G) : (((X3 ◇ X3) ◇ X4) ◇ ((X4 ◇ X4) ◇ X0)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq116 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq25 eq9 -- superposition 9,25, 25 into 9, unify on (0).2 in 25 and (0).1.1.1 in 9
  have eq138 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq116 eq10 -- backward demodulation 10,116
  subsumption eq138 eq15


@[equational_result]
theorem Equation2656_implies_Equation3457 (G : Type*) [Magma G] (h : Equation2656 G) : Equation3457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq35 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1 in 12
  have eq56 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq35 eq10 -- superposition 10,35, 35 into 10, unify on (0).2 in 35 and (0).2 in 10
  subsumption eq56 rfl


@[equational_result]
theorem Equation2656_implies_Equation2053 (G : Type*) [Magma G] (h : Equation2656 G) : Equation2053 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq19 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X4))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.1 in 11
  have eq25 (X0 X3 X4 : G) : (((X3 ◇ X3) ◇ X4) ◇ ((X4 ◇ X4) ◇ X0)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq101 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2)) = X1 := superpose eq25 eq25 -- superposition 25,25, 25 into 25, unify on (0).2 in 25 and (0).1.2.1 in 25
  have eq116 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq25 eq9 -- superposition 9,25, 25 into 9, unify on (0).2 in 25 and (0).1.1.1 in 9
  have eq398 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) = X0 := superpose eq116 eq15 -- superposition 15,116, 116 into 15, unify on (0).2 in 116 and (0).1.1 in 15
  have eq477 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.1 in 19
  have eq555 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq12 eq477 -- forward demodulation 477,12
  have eq818 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq9 eq398 -- superposition 398,9, 9 into 398, unify on (0).2 in 9 and (0).1.1.1 in 398
  have eq859 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq555 eq818 -- forward demodulation 818,555
  have eq860 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) = X1 := superpose eq859 eq101 -- backward demodulation 101,859
  have eq1183 : sK0 ≠ sK0 := superpose eq860 eq10 -- superposition 10,860, 860 into 10, unify on (0).2 in 860 and (0).2 in 10
  subsumption eq1183 rfl


@[equational_result]
theorem Equation2656_implies_Equation2036 (G : Type*) [Magma G] (h : Equation2656 G) : Equation2036 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq25 (X0 X3 X4 : G) : (((X3 ◇ X3) ◇ X4) ◇ ((X4 ◇ X4) ◇ X0)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq35 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1 in 12
  have eq119 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq25 eq35 -- superposition 35,25, 25 into 35, unify on (0).2 in 25 and (0).1 in 35
  have eq298 : sK0 ≠ sK0 := superpose eq119 eq10 -- superposition 10,119, 119 into 10, unify on (0).2 in 119 and (0).2 in 10
  subsumption eq298 rfl


@[equational_result]
theorem Equation2656_implies_Equation4282 (G : Type*) [Magma G] (h : Equation2656 G) : Equation4282 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X3)) ◇ X2) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq25 (X0 X3 X4 : G) : (((X3 ◇ X3) ◇ X4) ◇ ((X4 ◇ X4) ◇ X0)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq12 eq31 -- forward demodulation 31,12
  have eq93 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq12 eq25 -- superposition 25,12, 12 into 25, unify on (0).2 in 12 and (0).1.1.1 in 25
  have eq116 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq25 eq9 -- superposition 9,25, 25 into 9, unify on (0).2 in 25 and (0).1.1.1 in 9
  have eq173 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq16 eq16 -- superposition 16,16, 16 into 16, unify on (0).2 in 16 and (0).2.1 in 16
  have eq201 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq173 eq41 -- backward demodulation 41,173
  have eq417 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq116 eq201 -- superposition 201,116, 116 into 201, unify on (0).2 in 116 and (0).2.1.1 in 201
  have eq443 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq93 eq417 -- forward demodulation 417,93
  have eq444 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ sK0) := superpose eq443 eq10 -- backward demodulation 10,443
  subsumption eq444 eq443


@[equational_result]
theorem Equation2656_implies_Equation3256 (G : Type*) [Magma G] (h : Equation2656 G) : Equation3256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X3)) ◇ X2) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq25 (X0 X3 X4 : G) : (((X3 ◇ X3) ◇ X4) ◇ ((X4 ◇ X4) ◇ X0)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq12 eq31 -- forward demodulation 31,12
  have eq93 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq12 eq25 -- superposition 25,12, 12 into 25, unify on (0).2 in 12 and (0).1.1.1 in 25
  have eq116 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq25 eq9 -- superposition 9,25, 25 into 9, unify on (0).2 in 25 and (0).1.1.1 in 9
  have eq173 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq16 eq16 -- superposition 16,16, 16 into 16, unify on (0).2 in 16 and (0).2.1 in 16
  have eq201 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq173 eq41 -- backward demodulation 41,173
  have eq417 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := superpose eq116 eq201 -- superposition 201,116, 116 into 201, unify on (0).2 in 116 and (0).2.1.1 in 201
  have eq443 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq93 eq417 -- forward demodulation 417,93
  have eq634 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq443 eq10 -- superposition 10,443, 443 into 10, unify on (0).2 in 443 and (0).2 in 10
  subsumption eq634 rfl


@[equational_result]
theorem Equation2656_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2656 G) : Equation2847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq14 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1 in 8
  have eq24 (X0 X3 X4 : G) : (((X3 ◇ X3) ◇ X4) ◇ ((X4 ◇ X4) ◇ X0)) = X3 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.2 in 10
  have eq115 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq24 eq8 -- superposition 8,24, 24 into 8, unify on (0).2 in 24 and (0).1.1.1 in 8
  have eq137 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq115 eq9 -- backward demodulation 9,115
  subsumption eq137 eq14


@[equational_result]
theorem Equation2656_implies_Equation2054 (G : Type*) [Magma G] (h : Equation2656 G) : Equation2054 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq19 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X4))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.1 in 11
  have eq25 (X0 X3 X4 : G) : (((X3 ◇ X3) ◇ X4) ◇ ((X4 ◇ X4) ◇ X0)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq101 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2)) = X1 := superpose eq25 eq25 -- superposition 25,25, 25 into 25, unify on (0).2 in 25 and (0).1.2.1 in 25
  have eq116 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq25 eq9 -- superposition 9,25, 25 into 9, unify on (0).2 in 25 and (0).1.1.1 in 9
  have eq398 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) = X0 := superpose eq116 eq15 -- superposition 15,116, 116 into 15, unify on (0).2 in 116 and (0).1.1 in 15
  have eq477 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.1 in 19
  have eq555 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq12 eq477 -- forward demodulation 477,12
  have eq818 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq9 eq398 -- superposition 398,9, 9 into 398, unify on (0).2 in 9 and (0).1.1.1 in 398
  have eq859 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq555 eq818 -- forward demodulation 818,555
  have eq860 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) = X1 := superpose eq859 eq101 -- backward demodulation 101,859
  have eq1183 : sK0 ≠ sK0 := superpose eq860 eq10 -- superposition 10,860, 860 into 10, unify on (0).2 in 860 and (0).2 in 10
  subsumption eq1183 rfl


@[equational_result]
theorem Equation2656_implies_Equation2886 (G : Type*) [Magma G] (h : Equation2656 G) : Equation2886 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq25 (X0 X3 X4 : G) : (((X3 ◇ X3) ◇ X4) ◇ ((X4 ◇ X4) ◇ X0)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq116 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose eq25 eq9 -- superposition 9,25, 25 into 9, unify on (0).2 in 25 and (0).1.1.1 in 9
  have eq138 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq116 eq10 -- backward demodulation 10,116
  subsumption eq138 eq15


@[equational_result]
theorem Equation2055_implies_Equation2656 (G : Type*) [Magma G] (h : Equation2055 G) : Equation2656 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X3 : G) : (((X3 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = ((X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq38 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq17 eq13 -- superposition 13,17, 17 into 13, unify on (0).2 in 17 and (0).1.1.1 in 13
  have eq80 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq38 eq13 -- superposition 13,38, 38 into 13, unify on (0).2 in 38 and (0).1.1 in 13
  have eq86 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq38 eq9 -- superposition 9,38, 38 into 9, unify on (0).2 in 38 and (0).1.1.1 in 9
  have eq94 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq9 eq86 -- forward demodulation 86,9
  have eq95 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq12 eq94 -- forward demodulation 94,12
  have eq136 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq80 eq11 -- superposition 11,80, 80 into 11, unify on (0).2 in 80 and (0).1.1 in 11
  have eq148 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq136 -- forward demodulation 136,9
  have eq149 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq95 eq148 -- forward demodulation 148,95
  have eq158 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq149 eq22 -- backward demodulation 22,149
  have eq166 (X0 X1 X3 : G) : (((X3 ◇ X3) ◇ (X0 ◇ X1)) ◇ X0) = X3 := superpose eq158 eq13 -- backward demodulation 13,158
  have eq194 : sK0 ≠ sK0 := superpose eq166 eq10 -- superposition 10,166, 166 into 10, unify on (0).2 in 166 and (0).2 in 10
  subsumption eq194 rfl


@[equational_result]
theorem Equation2055_implies_Equation3257 (G : Type*) [Magma G] (h : Equation2055 G) : Equation3257 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2055_implies_Equation308 (G : Type*) [Magma G] (h : Equation2055 G) : Equation308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation2055_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2055 G) : Equation2644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 (X0 X1 X3 : G) : (((X3 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) ◇ X0) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq16 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.1 in 8
  have eq37 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1.1 in 12
  have eq62 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq79 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq37 eq12 -- superposition 12,37, 37 into 12, unify on (0).2 in 37 and (0).1.1 in 12
  have eq85 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq37 eq8 -- superposition 8,37, 37 into 8, unify on (0).2 in 37 and (0).1.1.1 in 8
  have eq93 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq8 eq85 -- forward demodulation 85,8
  have eq94 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq93 -- forward demodulation 93,11
  have eq95 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq94 eq62 -- backward demodulation 62,94
  have eq99 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq95 eq9 -- backward demodulation 9,95
  subsumption eq99 eq79


@[equational_result]
theorem Equation2055_implies_Equation4314 (G : Type*) [Magma G] (h : Equation2055 G) : Equation4314 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X3 : G) : (((X3 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = ((X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq38 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq17 eq13 -- superposition 13,17, 17 into 13, unify on (0).2 in 17 and (0).1.1.1 in 13
  have eq63 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq80 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq38 eq13 -- superposition 13,38, 38 into 13, unify on (0).2 in 38 and (0).1.1 in 13
  have eq86 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq38 eq9 -- superposition 9,38, 38 into 9, unify on (0).2 in 38 and (0).1.1.1 in 9
  have eq94 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq9 eq86 -- forward demodulation 86,9
  have eq95 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq12 eq94 -- forward demodulation 94,12
  have eq96 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq95 eq63 -- backward demodulation 63,95
  have eq110 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq96 eq9 -- superposition 9,96, 96 into 9, unify on (0).2 in 96 and (0).1.1.1 in 9
  have eq124 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq110 -- forward demodulation 110,9
  have eq136 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq80 eq11 -- superposition 11,80, 80 into 11, unify on (0).2 in 80 and (0).1.1 in 11
  have eq148 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq136 -- forward demodulation 136,9
  have eq149 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq95 eq148 -- forward demodulation 148,95
  have eq158 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq149 eq22 -- backward demodulation 22,149
  have eq166 (X0 X1 X3 : G) : (((X3 ◇ X3) ◇ (X0 ◇ X1)) ◇ X0) = X3 := superpose eq158 eq13 -- backward demodulation 13,158
  have eq194 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X2)) = ((X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) ◇ (X1 ◇ X3)) := superpose eq166 eq9 -- superposition 9,166, 166 into 9, unify on (0).2 in 166 and (0).1.1.1 in 9
  have eq207 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X3)) = ((X0 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq124 eq194 -- forward demodulation 194,124
  have eq924 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq17 eq207 -- superposition 207,17, 17 into 207, unify on (0).2 in 17 and (0).1.1 in 207
  have eq1296 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq924 eq10 -- superposition 10,924, 924 into 10, unify on (0).2 in 924 and (0).2 in 10
  subsumption eq1296 eq924


@[equational_result]
theorem Equation268_implies_Equation2047 (G : Type*) [Magma G] (h : Equation268 G) : Equation2047 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq22 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ X0) ◇ (sK2 ◇ sK1)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq22 eq13


@[equational_result]
theorem Equation268_implies_Equation3527 (G : Type*) [Magma G] (h : Equation268 G) : Equation3527 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq22 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq22 eq12


@[equational_result]
theorem Equation268_implies_Equation3266 (G : Type*) [Magma G] (h : Equation268 G) : Equation3266 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq22 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 eq12


@[equational_result]
theorem Equation268_implies_Equation2868 (G : Type*) [Magma G] (h : Equation268 G) : Equation2868 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq22 (X0 : G) : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq22 eq13


@[equational_result]
theorem Equation268_implies_Equation4361 (G : Type*) [Magma G] (h : Equation268 G) : Equation4361 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ sK4)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ X0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 eq12


@[equational_result]
theorem Equation2047_implies_Equation268 (G : Type*) [Magma G] (h : Equation2047 G) : Equation268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ (X2 ◇ X1)) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X3 X4 : G) : (((X3 ◇ X3) ◇ X0) ◇ X4) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq18 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq23 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK2) ◇ sK2) := superpose eq18 eq10 -- backward demodulation 10,18
  subsumption eq23 eq16


@[equational_result]
theorem Equation2047_implies_Equation3261 (G : Type*) [Magma G] (h : Equation2047 G) : Equation3261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ (X2 ◇ X1)) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq23 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq18 eq10 -- backward demodulation 10,18
  subsumption eq23 eq18


@[equational_result]
theorem Equation2682_implies_Equation2667 (G : Type*) [Magma G] (h : Equation2682 G) : Equation2667 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X3 X4 X5 : G) : (((X3 ◇ X4) ◇ X0) ◇ X5) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X4 : G) : (X0 ◇ X1) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ (sK0 ◇ sK2)) ◇ sK2) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq20 eq12


@[equational_result]
theorem Equation267_implies_Equation2075 (G : Type*) [Magma G] (h : Equation267 G) : Equation2075 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq22 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ X0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 eq13


@[equational_result]
theorem Equation2848_implies_Equation2690 (G : Type*) [Magma G] (h : Equation2848 G) : Equation2690 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 (X0 X1 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq22 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq23 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq42 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq23 eq23 -- superposition 23,23, 23 into 23, unify on (0).2 in 23 and (0).2 in 23
  have eq47 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ X1) ◇ X2) := superpose eq23 eq13 -- superposition 13,23, 23 into 13, unify on (0).2 in 23 and (0).2.1 in 13
  have eq80 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ X0) ◇ sK3) := superpose eq42 eq10 -- superposition 10,42, 42 into 10, unify on (0).2 in 42 and (0).2.1 in 10
  have eq106 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq47 eq47 -- superposition 47,47, 47 into 47, unify on (0).2 in 47 and (0).1.1.2 in 47
  have eq150 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq47 eq106 -- forward demodulation 106,47
  have eq151 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq150 -- forward demodulation 150,9
  have eq162 (X0 X1 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ X1) ◇ sK3) := superpose eq42 eq80 -- superposition 80,42, 42 into 80, unify on (0).2 in 42 and (0).2.1.1 in 80
  subsumption eq162 eq151


@[equational_result]
theorem Equation2680_implies_Equation2848 (G : Type*) [Magma G] (h : Equation2680 G) : Equation2848 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ X3) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq37 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq12 eq16 -- superposition 16,12, 12 into 16, unify on (0).2 in 12 and (0).1 in 16
  have eq46 (X0 : G) : sK0 ≠ (((sK0 ◇ (sK0 ◇ X0)) ◇ sK0) ◇ sK1) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1.1.2 in 10
  subsumption eq46 eq37


@[equational_result]
theorem Equation2892_implies_Equation3331 (G : Type*) [Magma G] (h : Equation2892 G) : Equation3331 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X3 ◇ X0) ◇ X2) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq22 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq32 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ X0) := superpose eq16 eq22 -- superposition 22,16, 16 into 22, unify on (0).2 in 16 and (0).2 in 22
  subsumption eq32 eq16


@[equational_result]
theorem Equation2892_implies_Equation2680 (G : Type*) [Magma G] (h : Equation2892 G) : Equation2680 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X3 ◇ X0) ◇ X2) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq22 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq23 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1 in 16
  have eq32 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ X0) ◇ sK1) := superpose eq16 eq22 -- superposition 22,16, 16 into 22, unify on (0).2 in 16 and (0).2.1 in 22
  subsumption eq32 eq23


@[equational_result]
theorem Equation2684_implies_Equation2892 (G : Type*) [Magma G] (h : Equation2684 G) : Equation2892 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X3 ◇ X1) ◇ X0) ◇ X1) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq22 : sK0 ≠ (((sK0 ◇ sK2) ◇ sK2) ◇ sK2) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq22 eq12


@[equational_result]
theorem Equation2081_implies_Equation2877 (G : Type*) [Magma G] (h : Equation2081 G) : Equation2877 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X4) ◇ (X4 ◇ X5)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X0 ◇ ((X2 ◇ X3) ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X0 X1 X2 X3 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X5) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq62 (X0 X1 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ (X0 ◇ X1)) ◇ sK2) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2.1 in 10
  subsumption eq62 eq23


@[equational_result]
theorem Equation2067_implies_Equation2689 (G : Type*) [Magma G] (h : Equation2067 G) : Equation2689 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X3 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1 in 12
  have eq21 (X0 X1 X3 : G) : (((X3 ◇ X1) ◇ X1) ◇ X0) = X3 := superpose eq13 eq12 -- backward demodulation 12,13
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq21 eq21 -- superposition 21,21, 21 into 21, unify on (0).2 in 21 and (0).1.1 in 21
  have eq36 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X1) ◇ X3) = X0 := superpose eq24 eq21 -- superposition 21,24, 24 into 21, unify on (0).2 in 24 and (0).1.1.1 in 21
  have eq42 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ X0) ◇ sK2) := superpose eq24 eq10 -- superposition 10,24, 24 into 10, unify on (0).2 in 24 and (0).2.1 in 10
  subsumption eq42 eq36


@[equational_result]
theorem Equation2654_implies_Equation2864 (G : Type*) [Magma G] (h : Equation2654 G) : Equation2864 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq12


@[equational_result]
theorem Equation2086_implies_Equation262 (G : Type*) [Magma G] (h : Equation2086 G) : Equation262 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq13 (X0 X5 X6 X7 : G) : (((X5 ◇ X6) ◇ X7) ◇ X0) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq42 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq42 rfl


@[equational_result]
theorem Equation2668_implies_Equation2086 (G : Type*) [Magma G] (h : Equation2668 G) : Equation2086 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK3 ◇ sK4)) := mod_symm nh
  have eq13 (X0 X1 X4 : G) : (X0 ◇ X1) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq26 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq28 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK2) ◇ (sK3 ◇ sK4)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq28 eq26


@[equational_result]
theorem Equation2668_implies_Equation3317 (G : Type*) [Magma G] (h : Equation2668 G) : Equation3317 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq13 (X0 X1 X4 : G) : (X0 ◇ X1) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq26 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ X0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.2 in 10
  subsumption eq26 eq13


@[equational_result]
theorem Equation2668_implies_Equation3462 (G : Type*) [Magma G] (h : Equation2668 G) : Equation3462 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X4 : G) : (X0 ◇ X1) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation2668_implies_Equation2654 (G : Type*) [Magma G] (h : Equation2668 G) : Equation2654 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X4 : G) : (X0 ◇ X1) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq25 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq26 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq26 eq25


@[equational_result]
theorem Equation265_implies_Equation2668 (G : Type*) [Magma G] (h : Equation265 G) : Equation2668 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq19 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X1) ◇ X3) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq22 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ X0) ◇ sK3) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq22 eq19


@[equational_result]
theorem Equation265_implies_Equation4283 (G : Type*) [Magma G] (h : Equation265 G) : Equation4283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq22 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ X0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 eq12


@[equational_result]
theorem Equation2690_implies_Equation265 (G : Type*) [Magma G] (h : Equation2690 G) : Equation265 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X3 X4 X5 : G) : (((X3 ◇ X4) ◇ X0) ◇ X5) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X4 : G) : (X0 ◇ X1) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK1) ◇ sK2) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq24 eq12


@[equational_result]
theorem Equation2069_implies_Equation2690 (G : Type*) [Magma G] (h : Equation2069 G) : Equation2690 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) ◇ sK3) := mod_symm nh
  have eq13 (X0 X4 X5 : G) : (((X4 ◇ X5) ◇ X5) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq69 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X1) ◇ X3) = X0 := superpose eq17 eq13 -- superposition 13,17, 17 into 13, unify on (0).2 in 17 and (0).1.1.1 in 13
  have eq75 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ X0) ◇ sK3) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2.1 in 10
  subsumption eq75 eq69


@[equational_result]
theorem Equation2870_implies_Equation2896 (G : Type*) [Magma G] (h : Equation2870 G) : Equation2896 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK3) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq29 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1 in 16
  have eq45 (X0 : G) : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ sK2) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1 in 10
  subsumption eq45 eq29


@[equational_result]
theorem Equation2692_implies_Equation2896 (G : Type*) [Magma G] (h : Equation2692 G) : Equation2896 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK3) ◇ sK2) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (((X4 ◇ X5) ◇ X0) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq54 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq12 eq17 -- superposition 17,12, 12 into 17, unify on (0).2 in 12 and (0).1 in 17
  have eq76 (X0 : G) : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK3) ◇ X0) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq76 eq54


@[equational_result]
theorem Equation2661_implies_Equation2692 (G : Type*) [Magma G] (h : Equation2661 G) : Equation2692 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK3)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq25 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq26 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK3)) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq26 eq25


@[equational_result]
theorem Equation2671_implies_Equation2661 (G : Type*) [Magma G] (h : Equation2671 G) : Equation2661 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq24 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq23


@[equational_result]
theorem Equation2671_implies_Equation2870 (G : Type*) [Magma G] (h : Equation2671 G) : Equation2870 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq26 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK2) ◇ sK2) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq26 eq24


@[equational_result]
theorem Equation2072_implies_Equation2067 (G : Type*) [Magma G] (h : Equation2072 G) : Equation2067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X1) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2.2 in 12
  have eq30 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq52 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X1) = ((X0 ◇ X3) ◇ X1) := superpose eq30 eq30 -- superposition 30,30, 30 into 30, unify on (0).2 in 30 and (0).2 in 30
  have eq73 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq30 eq9 -- superposition 9,30, 30 into 9, unify on (0).2 in 30 and (0).1.1 in 9
  have eq118 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = ((((X0 ◇ X1) ◇ X2) ◇ X4) ◇ X3) := superpose eq9 eq52 -- superposition 52,9, 9 into 52, unify on (0).2 in 9 and (0).1.1 in 52
  have eq168 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ X0) ◇ (sK2 ◇ sK1)) := superpose eq52 eq10 -- superposition 10,52, 52 into 10, unify on (0).2 in 52 and (0).2 in 10
  have eq203 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X0)) := superpose eq118 eq16 -- backward demodulation 16,118
  have eq226 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq73 eq203 -- forward demodulation 203,73
  subsumption eq168 eq226


@[equational_result]
theorem Equation2854_implies_Equation2657 (G : Type*) [Magma G] (h : Equation2854 G) : Equation2657 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 (X0 X1 X3 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq22 (X0 X1 X3 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (X0 ◇ X3) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq23 (X0 X1 X3 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (X0 ◇ X3) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq45 (X0 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ X2) := superpose eq23 eq23 -- superposition 23,23, 23 into 23, unify on (0).2 in 23 and (0).1 in 23
  have eq51 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X2) ◇ X3) := superpose eq23 eq13 -- superposition 13,23, 23 into 13, unify on (0).2 in 23 and (0).2.1 in 13
  have eq96 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ X0) ◇ sK2) := superpose eq45 eq10 -- superposition 10,45, 45 into 10, unify on (0).2 in 45 and (0).2.1 in 10
  have eq128 (X0 X1 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ X4) ◇ X5) = (((X0 ◇ (X0 ◇ X3)) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq51 eq51 -- superposition 51,51, 51 into 51, unify on (0).2 in 51 and (0).1.1 in 51
  have eq184 (X0 X1 X4 X5 : G) : (((X0 ◇ X1) ◇ X4) ◇ X5) = X0 := superpose eq9 eq128 -- forward demodulation 128,9
  have eq193 (X0 X1 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ X1) ◇ sK2) := superpose eq45 eq96 -- superposition 96,45, 45 into 96, unify on (0).2 in 45 and (0).2.1.1 in 96
  subsumption eq193 eq184


@[equational_result]
theorem Equation2884_implies_Equation2854 (G : Type*) [Magma G] (h : Equation2884 G) : Equation2854 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X3 ◇ X0) ◇ X3) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation2058_implies_Equation2695 (G : Type*) [Magma G] (h : Equation2058 G) : Equation2695 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK3)) ◇ sK4) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq81 (X0 X3 : G) : (X3 ◇ X3) = (X3 ◇ X0) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.2 in 14
  have eq114 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ (X3 ◇ X3)) := superpose eq81 eq11 -- backward demodulation 11,81
  have eq115 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK4) := superpose eq81 eq10 -- backward demodulation 10,81
  have eq121 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK4) := superpose eq81 eq115 -- forward demodulation 115,81
  have eq127 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq81 eq81 -- superposition 81,81, 81 into 81, unify on (0).2 in 81 and (0).1 in 81
  have eq156 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X3) = X0 := superpose eq9 eq127 -- superposition 127,9, 9 into 127, unify on (0).2 in 9 and (0).1 in 127
  have eq274 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK0) ◇ sK4) := superpose eq114 eq121 -- superposition 121,114, 114 into 121, unify on (0).2 in 114 and (0).2.1 in 121
  subsumption eq274 eq156


@[equational_result]
theorem Equation2877_implies_Equation2058 (G : Type*) [Magma G] (h : Equation2877 G) : Equation2058 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X1) = ((X0 ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X2) = ((((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X3) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq18 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ X4) ◇ X5) = (((X0 ◇ (X3 ◇ X3)) ◇ X3) ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq35 (X0 X2 X4 : G) : (X0 ◇ X2) = (X0 ◇ X4) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq36 (X0 X1 X4 X5 : G) : (((X0 ◇ X1) ◇ X4) ◇ X5) = X0 := superpose eq9 eq18 -- forward demodulation 18,9
  have eq104 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ X0) := superpose eq35 eq10 -- superposition 10,35, 35 into 10, unify on (0).2 in 35 and (0).2 in 10
  subsumption eq104 eq36


@[equational_result]
theorem Equation2861_implies_Equation3464 (G : Type*) [Magma G] (h : Equation2861 G) : Equation3464 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X4 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq19 (X0 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ X2) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1 in 13
  have eq32 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq32 eq19


@[equational_result]
theorem Equation2861_implies_Equation2881 (G : Type*) [Magma G] (h : Equation2861 G) : Equation2881 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X4 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq32 (X0 : G) : sK0 ≠ (((sK0 ◇ (sK0 ◇ X0)) ◇ sK2) ◇ sK3) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq32 eq9


@[equational_result]
theorem Equation2695_implies_Equation3263 (G : Type*) [Magma G] (h : Equation2695 G) : Equation3263 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq13 (X0 X1 X6 : G) : (X0 ◇ X1) = (X0 ◇ X6) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation2695_implies_Equation2897 (G : Type*) [Magma G] (h : Equation2695 G) : Equation2897 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK3) ◇ sK3) := mod_symm nh
  have eq12 (X0 X5 X6 X7 : G) : (((X5 ◇ X6) ◇ X0) ◇ X7) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X6 : G) : (X0 ◇ X1) = (X0 ◇ X6) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq22 (X0 : G) : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ sK3) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq22 eq12


@[equational_result]
theorem Equation2881_implies_Equation2885 (G : Type*) [Magma G] (h : Equation2881 G) : Equation2885 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) ◇ sK3) := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (((X3 ◇ X0) ◇ X4) ◇ X5) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2881_implies_Equation3463 (G : Type*) [Magma G] (h : Equation2881 G) : Equation3463 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (((X3 ◇ X0) ◇ X4) ◇ X5) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X4 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X4 : G) : (X0 ◇ X4) = (X0 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq47 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq47 eq17


@[equational_result]
theorem Equation2881_implies_Equation2079 (G : Type*) [Magma G] (h : Equation2881 G) : Equation2079 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (((X3 ◇ X0) ◇ X4) ◇ X5) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2080_implies_Equation2039 (G : Type*) [Magma G] (h : Equation2080 G) : Equation2039 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X3) ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq32 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq32 eq9


@[equational_result]
theorem Equation2080_implies_Equation4629 (G : Type*) [Magma G] (h : Equation2080 G) : Equation4629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X3) ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq27 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ X2) ◇ X3) = ((X0 ◇ X4) ◇ X5) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2 in 11
  have eq55 (X0 X2 X3 : G) : (X2 ◇ X3) = (X2 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq110 (X0 : G) : ((sK0 ◇ X0) ◇ sK0) ≠ ((sK0 ◇ X0) ◇ sK1) := superpose eq55 eq10 -- superposition 10,55, 55 into 10, unify on (0).2 in 55 and (0).1.1 in 10
  subsumption eq110 eq27


@[equational_result]
theorem Equation2075_implies_Equation2080 (G : Type*) [Magma G] (h : Equation2075 G) : Equation2080 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X3)) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq23 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (X0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq23 eq13


@[equational_result]
theorem Equation2075_implies_Equation2072 (G : Type*) [Magma G] (h : Equation2075 G) : Equation2072 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X3)) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq21 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (X0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq21 eq13


@[equational_result]
theorem Equation2689_implies_Equation2069 (G : Type*) [Magma G] (h : Equation2689 G) : Equation2069 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq24 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK1) ◇ (sK2 ◇ sK3)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1.1 in 10
  subsumption eq24 eq23


@[equational_result]
theorem Equation2664_implies_Equation2884 (G : Type*) [Magma G] (h : Equation2664 G) : Equation2884 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq22 (X0 : G) : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ sK2) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq22 eq21


@[equational_result]
theorem Equation2898_implies_Equation2664 (G : Type*) [Magma G] (h : Equation2898 G) : Equation2664 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X5 X6 X7 : G) : (((X5 ◇ X0) ◇ X6) ◇ X7) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2645_implies_Equation2859 (G : Type*) [Magma G] (h : Equation2645 G) : Equation2859 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK2) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq18 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq37 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ sK2) ◇ X0) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2 in 13
  subsumption eq37 eq18


@[equational_result]
theorem Equation2645_implies_Equation2855 (G : Type*) [Magma G] (h : Equation2645 G) : Equation2855 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq18 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq37 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ X0) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2 in 13
  subsumption eq37 eq18


@[equational_result]
theorem Equation2645_implies_Equation3533 (G : Type*) [Magma G] (h : Equation2645 G) : Equation3533 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation2645_implies_Equation2862 (G : Type*) [Magma G] (h : Equation2645 G) : Equation2862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq18 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq37 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ X0) ◇ sK0) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.1 in 13
  subsumption eq37 eq18


@[equational_result]
theorem Equation2645_implies_Equation2051 (G : Type*) [Magma G] (h : Equation2645 G) : Equation2051 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq34 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ X0) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2 in 13
  subsumption eq34 eq17


@[equational_result]
theorem Equation2645_implies_Equation2045 (G : Type*) [Magma G] (h : Equation2645 G) : Equation2045 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq18 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq22 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ X0)) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.2 in 13
  subsumption eq22 eq18


@[equational_result]
theorem Equation2645_implies_Equation269 (G : Type*) [Magma G] (h : Equation2645 G) : Equation269 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK2) ◇ sK3) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq18 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq37 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ X0) ◇ sK3) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.1 in 13
  subsumption eq37 eq18


@[equational_result]
theorem Equation2645_implies_Equation38 (G : Type*) [Magma G] (h : Equation2645 G) : Equation38 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq19 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2645_implies_Equation2078 (G : Type*) [Magma G] (h : Equation2645 G) : Equation2078 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK2) ◇ (sK2 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq18 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq37 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ sK2) ◇ X0) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2 in 13
  subsumption eq37 eq18


@[equational_result]
theorem Equation2897_implies_Equation309 (G : Type*) [Magma G] (h : Equation2897 G) : Equation309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (((X4 ◇ X0) ◇ X5) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq44 (X0 X1 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ X1)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq44 eq17


@[equational_result]
theorem Equation2897_implies_Equation2645 (G : Type*) [Magma G] (h : Equation2897 G) : Equation2645 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (((X4 ◇ X0) ◇ X5) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq54 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).1 in 17
  have eq65 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ (sK0 ◇ X0)) ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2.1.1 in 10
  subsumption eq65 eq54


@[equational_result]
theorem Equation2651_implies_Equation2898 (G : Type*) [Magma G] (h : Equation2651 G) : Equation2898 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK3) ◇ sK4) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK3) ◇ sK4) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq12


@[equational_result]
theorem Equation2879_implies_Equation2651 (G : Type*) [Magma G] (h : Equation2879 G) : Equation2651 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X1) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq28 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ (X0 ◇ X0)) ◇ sK2) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq28 eq21


@[equational_result]
theorem Equation2871_implies_Equation2889 (G : Type*) [Magma G] (h : Equation2871 G) : Equation2889 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) ◇ sK3) := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (((X3 ◇ X0) ◇ X4) ◇ X5) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2871_implies_Equation2059 (G : Type*) [Magma G] (h : Equation2871 G) : Equation2059 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (((X3 ◇ X0) ◇ X4) ◇ X5) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2083_implies_Equation2871 (G : Type*) [Magma G] (h : Equation2083 G) : Equation2871 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ X1) = (X0 ◇ (X4 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 X1 X2 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X4) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq27 (X0 X1 : G) : sK0 ≠ (((sK0 ◇ (X0 ◇ X1)) ◇ sK2) ◇ sK3) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1.1 in 10
  subsumption eq27 eq20


@[equational_result]
theorem Equation2083_implies_Equation2879 (G : Type*) [Magma G] (h : Equation2083 G) : Equation2879 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ X1) = (X0 ◇ (X4 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 X1 X2 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X4) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq27 (X0 X1 : G) : sK0 ≠ (((sK0 ◇ (X0 ◇ X1)) ◇ sK2) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1.1 in 10
  subsumption eq27 eq20


@[equational_result]
theorem Equation2083_implies_Equation2684 (G : Type*) [Magma G] (h : Equation2083 G) : Equation2684 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ X1) = (X0 ◇ (X4 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 X1 X2 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X4) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq26 (X0 X1 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ (X0 ◇ X1)) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq26 eq20


@[equational_result]
theorem Equation2039_implies_Equation2083 (G : Type*) [Magma G] (h : Equation2039 G) : Equation2083 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK3 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X3 : G) : (((X3 ◇ X3) ◇ X3) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1 in 12
  have eq26 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1 in 12
  have eq37 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq9 eq26 -- forward demodulation 26,9
  have eq48 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq37 eq37 -- superposition 37,37, 37 into 37, unify on (0).2 in 37 and (0).2 in 37
  have eq130 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ X0) := superpose eq48 eq10 -- superposition 10,48, 48 into 10, unify on (0).2 in 48 and (0).2 in 10
  have eq174 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X2) := superpose eq37 eq13 -- superposition 13,37, 37 into 13, unify on (0).2 in 37 and (0).2.1 in 13
  have eq206 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ X0) := superpose eq174 eq130 -- backward demodulation 130,174
  subsumption eq206 eq12


@[equational_result]
theorem Equation2039_implies_Equation267 (G : Type*) [Magma G] (h : Equation2039 G) : Equation267 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X3 : G) : (((X3 ◇ X3) ◇ X3) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1 in 12
  have eq26 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1 in 12
  have eq37 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq9 eq26 -- forward demodulation 26,9
  have eq48 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq37 eq37 -- superposition 37,37, 37 into 37, unify on (0).2 in 37 and (0).2 in 37
  have eq120 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ X0) := superpose eq48 eq10 -- superposition 10,48, 48 into 10, unify on (0).2 in 48 and (0).2 in 10
  have eq172 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X2) := superpose eq37 eq13 -- superposition 13,37, 37 into 13, unify on (0).2 in 37 and (0).2.1 in 13
  have eq204 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ X0) := superpose eq172 eq120 -- backward demodulation 120,172
  subsumption eq204 eq12


@[equational_result]
theorem Equation2885_implies_Equation2039 (G : Type*) [Magma G] (h : Equation2885 G) : Equation2039 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (((X4 ◇ X0) ◇ X4) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation2885_implies_Equation4286 (G : Type*) [Magma G] (h : Equation2885 G) : Equation4286 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (((X4 ◇ X0) ◇ X4) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq75 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ X0) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq75 eq16


@[equational_result]
theorem Equation2885_implies_Equation3534 (G : Type*) [Magma G] (h : Equation2885 G) : Equation3534 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (((X4 ◇ X0) ◇ X4) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq75 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK1) ◇ X0)) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2.2 in 10
  subsumption eq75 eq17


@[equational_result]
theorem Equation2678_implies_Equation2049 (G : Type*) [Magma G] (h : Equation2678 G) : Equation2049 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq13 (X0 X1 X4 : G) : (X0 ◇ X1) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq26 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK1) ◇ (sK2 ◇ sK3)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq26 eq24


@[equational_result]
theorem Equation2693_implies_Equation2678 (G : Type*) [Magma G] (h : Equation2693 G) : Equation2678 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq24 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq14


@[equational_result]
theorem Equation2867_implies_Equation2693 (G : Type*) [Magma G] (h : Equation2867 G) : Equation2693 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK3)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = ((X0 ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X2) = ((((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X3) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq17 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ X4) ◇ X5) = (((X0 ◇ (X3 ◇ X0)) ◇ X3) ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq32 (X0 X2 X4 : G) : (X0 ◇ X2) = (X0 ◇ X4) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq33 (X0 X1 X4 X5 : G) : (((X0 ◇ X1) ◇ X4) ◇ X5) = X0 := superpose eq9 eq17 -- forward demodulation 17,9
  have eq95 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ X0) ◇ sK2) := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2.1 in 10
  subsumption eq95 eq33


@[equational_result]
theorem Equation2867_implies_Equation4603 (G : Type*) [Magma G] (h : Equation2867 G) : Equation4603 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = ((X0 ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X2) = ((((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X3) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq18 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ X2) ◇ X3) = ((X0 ◇ X4) ◇ X5) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq32 (X0 X2 X4 : G) : (X0 ◇ X2) = (X0 ◇ X4) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq96 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ X0) ◇ sK2) := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2.1 in 10
  subsumption eq96 eq18


@[equational_result]
theorem Equation2657_implies_Equation2863 (G : Type*) [Magma G] (h : Equation2657 G) : Equation2863 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X3 ◇ X3) ◇ X0) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq19 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq19 eq11


@[equational_result]
theorem Equation2657_implies_Equation2867 (G : Type*) [Magma G] (h : Equation2657 G) : Equation2867 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X3 ◇ X3) ◇ X0) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq19 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK2) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq19 eq11


@[equational_result]
theorem Equation2059_implies_Equation2657 (G : Type*) [Magma G] (h : Equation2059 G) : Equation2657 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X4 X5 : G) : (((X4 ◇ X5) ◇ X4) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X4 X5 : G) : (X4 ◇ X5) = (X4 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq39 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) = X0 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).1.1 in 13
  have eq72 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) ◇ X0) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq72 eq39


@[equational_result]
theorem Equation2648_implies_Equation2853 (G : Type*) [Magma G] (h : Equation2648 G) : Equation2853 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1 in 13
  have eq22 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq44 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ X0) ◇ sK1) := superpose eq18 eq16 -- superposition 16,18, 18 into 16, unify on (0).2 in 18 and (0).2.1 in 16
  subsumption eq44 eq22


@[equational_result]
theorem Equation2648_implies_Equation2081 (G : Type*) [Magma G] (h : Equation2648 G) : Equation2081 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq13 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK2) ◇ (sK2 ◇ sK3)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq17 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK2) ◇ (sK2 ◇ sK2)) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq23 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq29 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ sK2) ◇ (sK2 ◇ X0)) := superpose eq13 eq17 -- superposition 17,13, 13 into 17, unify on (0).2 in 13 and (0).2.2 in 17
  subsumption eq29 eq23


@[equational_result]
theorem Equation2674_implies_Equation2898 (G : Type*) [Magma G] (h : Equation2674 G) : Equation2898 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK3) ◇ sK4) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq24 (X0 : G) : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ sK4) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq24 eq23


@[equational_result]
theorem Equation2896_implies_Equation2055 (G : Type*) [Magma G] (h : Equation2896 G) : Equation2055 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X2 X4 X5 : G) : (((X4 ◇ X0) ◇ X5) ◇ X2) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2896_implies_Equation2674 (G : Type*) [Magma G] (h : Equation2896 G) : Equation2674 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X4 X5 : G) : (((X4 ◇ X0) ◇ X5) ◇ X2) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation2896_implies_Equation259 (G : Type*) [Magma G] (h : Equation2896 G) : Equation259 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X4 X5 : G) : (((X4 ◇ X0) ◇ X5) ◇ X2) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2681_implies_Equation2873 (G : Type*) [Magma G] (h : Equation2681 G) : Equation2873 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ X2) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq24 (X0 : G) : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq24 eq23


@[equational_result]
theorem Equation2681_implies_Equation264 (G : Type*) [Magma G] (h : Equation2681 G) : Equation264 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ X2) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq24 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq24 eq23


@[equational_result]
theorem Equation2681_implies_Equation2064 (G : Type*) [Magma G] (h : Equation2681 G) : Equation2064 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ X2) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq25 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK1) ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq25 eq24


@[equational_result]
theorem Equation2681_implies_Equation2648 (G : Type*) [Magma G] (h : Equation2681 G) : Equation2648 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ X2) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq24 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq23


@[equational_result]
theorem Equation2859_implies_Equation3466 (G : Type*) [Magma G] (h : Equation2859 G) : Equation3466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq26 eq16


@[equational_result]
theorem Equation2859_implies_Equation2647 (G : Type*) [Magma G] (h : Equation2859 G) : Equation2647 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X1) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq38 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ (sK0 ◇ sK1)) ◇ sK1) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1.1 in 10
  subsumption eq38 eq21


@[equational_result]
theorem Equation2859_implies_Equation3321 (G : Type*) [Magma G] (h : Equation2859 G) : Equation3321 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq26 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq26 eq16


@[equational_result]
theorem Equation2859_implies_Equation2070 (G : Type*) [Magma G] (h : Equation2859 G) : Equation2070 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X1) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq38 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK2) ◇ (sK0 ◇ sK0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1.1 in 10
  subsumption eq38 eq21


@[equational_result]
theorem Equation2859_implies_Equation3318 (G : Type*) [Magma G] (h : Equation2859 G) : Equation3318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq23 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq23 eq16


@[equational_result]
theorem Equation2859_implies_Equation3324 (G : Type*) [Magma G] (h : Equation2859 G) : Equation3324 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq26 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq26 eq16


@[equational_result]
theorem Equation2859_implies_Equation3537 (G : Type*) [Magma G] (h : Equation2859 G) : Equation3537 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq26 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq26 eq16


@[equational_result]
theorem Equation2859_implies_Equation3322 (G : Type*) [Magma G] (h : Equation2859 G) : Equation3322 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq26 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq26 eq16


@[equational_result]
theorem Equation2859_implies_Equation3338 (G : Type*) [Magma G] (h : Equation2859 G) : Equation3338 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq26 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq26 eq16


@[equational_result]
theorem Equation2859_implies_Equation4360 (G : Type*) [Magma G] (h : Equation2859 G) : Equation4360 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq26 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq26 eq16


@[equational_result]
theorem Equation2859_implies_Equation3267 (G : Type*) [Magma G] (h : Equation2859 G) : Equation3267 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq26 eq16


@[equational_result]
theorem Equation2859_implies_Equation2666 (G : Type*) [Magma G] (h : Equation2859 G) : Equation2666 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X1) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq38 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ (sK0 ◇ sK2)) ◇ sK1) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1.1 in 10
  subsumption eq38 eq21


@[equational_result]
theorem Equation2859_implies_Equation3522 (G : Type*) [Magma G] (h : Equation2859 G) : Equation3522 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq25 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq25 eq16


@[equational_result]
theorem Equation2859_implies_Equation311 (G : Type*) [Magma G] (h : Equation2859 G) : Equation311 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq26 eq16


@[equational_result]
theorem Equation2859_implies_Equation4601 (G : Type*) [Magma G] (h : Equation2859 G) : Equation4601 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X1) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq38 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ X0) ◇ sK0) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1 in 10
  have eq57 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X4) ◇ X5) := superpose eq21 eq21 -- superposition 21,21, 21 into 21, unify on (0).2 in 21 and (0).1.1.1 in 21
  have eq80 (X0 X1 : G) : ((sK0 ◇ X1) ◇ sK0) ≠ ((sK0 ◇ X0) ◇ sK1) := superpose eq16 eq38 -- superposition 38,16, 16 into 38, unify on (0).2 in 16 and (0).1.1 in 38
  subsumption eq80 eq57


@[equational_result]
theorem Equation2859_implies_Equation3461 (G : Type*) [Magma G] (h : Equation2859 G) : Equation3461 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq25 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq25 eq16


@[equational_result]
theorem Equation2859_implies_Equation329 (G : Type*) [Magma G] (h : Equation2859 G) : Equation329 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq26 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq26 eq16


@[equational_result]
theorem Equation2859_implies_Equation4316 (G : Type*) [Magma G] (h : Equation2859 G) : Equation4316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq26 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq26 eq16


