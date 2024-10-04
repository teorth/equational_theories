import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation4481_implies_Equation4489 (G : Type*) [Magma G] (h : Equation4481 G) : Equation4489 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq37 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK0) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq69 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X5) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  have eq354 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((((sK2 ◇ sK0) ◇ X0) ◇ X1) ◇ X2) := superpose eq68 eq37 -- superposition 37,68, 68 into 37, unify on (0).2 in 68 and (0).2 in 37
  subsumption eq354 eq69


@[equational_result]
theorem Equation4481_implies_Equation4394 (G : Type*) [Magma G] (h : Equation4481 G) : Equation4394 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK2) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq33 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK2) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq69 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X5) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  have eq357 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((((sK1 ◇ sK2) ◇ X0) ◇ X1) ◇ X2) := superpose eq68 eq33 -- superposition 33,68, 68 into 33, unify on (0).2 in 68 and (0).2 in 33
  subsumption eq357 eq69


@[equational_result]
theorem Equation4481_implies_Equation4478 (G : Type*) [Magma G] (h : Equation4481 G) : Equation4478 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq33 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq69 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X5) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  have eq357 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((((sK0 ◇ sK2) ◇ X0) ◇ X1) ◇ X2) := superpose eq68 eq33 -- superposition 33,68, 68 into 33, unify on (0).2 in 68 and (0).2 in 33
  subsumption eq357 eq69


@[equational_result]
theorem Equation4481_implies_Equation4502 (G : Type*) [Magma G] (h : Equation4481 G) : Equation4502 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq33 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq69 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X5) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  have eq357 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((((sK2 ◇ sK3) ◇ X0) ◇ X1) ◇ X2) := superpose eq68 eq33 -- superposition 33,68, 68 into 33, unify on (0).2 in 68 and (0).2 in 33
  subsumption eq357 eq69


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
theorem Equation4481_implies_Equation4503 (G : Type*) [Magma G] (h : Equation4481 G) : Equation4503 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq33 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq69 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X5) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  have eq357 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((((sK2 ◇ sK3) ◇ X0) ◇ X1) ◇ X2) := superpose eq68 eq33 -- superposition 33,68, 68 into 33, unify on (0).2 in 68 and (0).2 in 33
  subsumption eq357 eq69


@[equational_result]
theorem Equation4481_implies_Equation4474 (G : Type*) [Magma G] (h : Equation4481 G) : Equation4474 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq33 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq69 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X5) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  have eq357 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((((sK0 ◇ sK1) ◇ X0) ◇ X1) ◇ X2) := superpose eq68 eq33 -- superposition 33,68, 68 into 33, unify on (0).2 in 68 and (0).2 in 33
  subsumption eq357 eq69


@[equational_result]
theorem Equation2186_implies_Equation1894 (G : Type*) [Magma G] (h : Equation2186 G) : Equation1894 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq43 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2.1 in 14
  have eq282 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq43 eq10 -- superposition 10,43, 43 into 10, unify on (0).2 in 43 and (0).2 in 10
  subsumption eq282 eq12


@[equational_result]
theorem Equation2186_implies_Equation3278 (G : Type*) [Magma G] (h : Equation2186 G) : Equation3278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation2186_implies_Equation3414 (G : Type*) [Magma G] (h : Equation2186 G) : Equation3414 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation2186_implies_Equation3955 (G : Type*) [Magma G] (h : Equation2186 G) : Equation3955 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq43 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2.1 in 14
  have eq285 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq43 eq10 -- superposition 10,43, 43 into 10, unify on (0).2 in 43 and (0).2 in 10
  subsumption eq285 rfl


@[equational_result]
theorem Equation2186_implies_Equation1850 (G : Type*) [Magma G] (h : Equation2186 G) : Equation1850 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq43 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2.1 in 14
  have eq282 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq43 eq10 -- superposition 10,43, 43 into 10, unify on (0).2 in 43 and (0).2 in 10
  subsumption eq282 eq12


@[equational_result]
theorem Equation2186_implies_Equation4023 (G : Type*) [Magma G] (h : Equation2186 G) : Equation4023 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 rfl


@[equational_result]
theorem Equation2186_implies_Equation3880 (G : Type*) [Magma G] (h : Equation2186 G) : Equation3880 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq43 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2.1 in 14
  have eq285 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq43 eq10 -- superposition 10,43, 43 into 10, unify on (0).2 in 43 and (0).2 in 10
  subsumption eq285 rfl


@[equational_result]
theorem Equation2186_implies_Equation1285 (G : Type*) [Magma G] (h : Equation2186 G) : Equation1285 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq17 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq12


@[equational_result]
theorem Equation2186_implies_Equation1793 (G : Type*) [Magma G] (h : Equation2186 G) : Equation1793 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK2 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq41 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose eq12 eq14 -- superposition 14,12, 12 into 14, unify on (0).2 in 12 and (0).2.1.1 in 14
  have eq61 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK0)) := superpose eq41 eq10 -- backward demodulation 10,41
  subsumption eq61 eq12


@[equational_result]
theorem Equation2186_implies_Equation1241 (G : Type*) [Magma G] (h : Equation2186 G) : Equation1241 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq17 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq12


@[equational_result]
theorem Equation2186_implies_Equation1374 (G : Type*) [Magma G] (h : Equation2186 G) : Equation1374 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK1) ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq17 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq12


@[equational_result]
theorem Equation566_implies_Equation364 (G : Type*) [Magma G] (h : Equation566 G) : Equation364 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X1 X2 X3 : G) : (X2 ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation566_implies_Equation4677 (G : Type*) [Magma G] (h : Equation566 G) : Equation4677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK1 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq13 (X1 X2 X3 : G) : (X2 ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ ((X0 ◇ sK0) ◇ sK2) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation566_implies_Equation4146 (G : Type*) [Magma G] (h : Equation566 G) : Equation4146 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq13 (X1 X2 X3 : G) : (X2 ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation566_implies_Equation500 (G : Type*) [Magma G] (h : Equation566 G) : Equation500 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq13 (X1 X2 X3 : G) : (X2 ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq20 (X0 : G) : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (X0 ◇ sK0)))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.2.2 in 10
  subsumption eq20 eq14


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
theorem Equation1027_implies_Equation2036 (G : Type*) [Magma G] (h : Equation1027 G) : Equation2036 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq19 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq20 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq14 eq19 -- forward demodulation 19,14
  subsumption eq20 eq12


@[equational_result]
theorem Equation1027_implies_Equation308 (G : Type*) [Magma G] (h : Equation1027 G) : Equation308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq23 : sK0 ≠ sK0 := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  subsumption eq23 rfl


@[equational_result]
theorem Equation1027_implies_Equation418 (G : Type*) [Magma G] (h : Equation1027 G) : Equation418 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation1027_implies_Equation3320 (G : Type*) [Magma G] (h : Equation1027 G) : Equation3320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 rfl


@[equational_result]
theorem Equation1027_implies_Equation1022 (G : Type*) [Magma G] (h : Equation1027 G) : Equation1022 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation1027_implies_Equation626 (G : Type*) [Magma G] (h : Equation1027 G) : Equation626 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation1027_implies_Equation3256 (G : Type*) [Magma G] (h : Equation1027 G) : Equation3256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq23 : sK0 ≠ sK0 := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  subsumption eq23 rfl


@[equational_result]
theorem Equation1027_implies_Equation3660 (G : Type*) [Magma G] (h : Equation1027 G) : Equation3660 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq19 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq19 eq12


@[equational_result]
theorem Equation1027_implies_Equation1838 (G : Type*) [Magma G] (h : Equation1027 G) : Equation1838 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation1027_implies_Equation425 (G : Type*) [Magma G] (h : Equation1027 G) : Equation425 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation1027_implies_Equation1224 (G : Type*) [Magma G] (h : Equation1027 G) : Equation1224 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq19 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq20 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq14 eq19 -- forward demodulation 19,14
  subsumption eq20 eq12


@[equational_result]
theorem Equation1027_implies_Equation420 (G : Type*) [Magma G] (h : Equation1027 G) : Equation420 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation1027_implies_Equation4065 (G : Type*) [Magma G] (h : Equation1027 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1.2 in 11
  have eq18 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq13 eq9 -- backward demodulation 9,13
  have eq19 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq18 -- forward demodulation 18,13
  subsumption eq19 eq13


@[equational_result]
theorem Equation1027_implies_Equation1837 (G : Type*) [Magma G] (h : Equation1027 G) : Equation1837 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation102_implies_Equation614 (G : Type*) [Magma G] (h : Equation102 G) : Equation614 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq10 : sK0 ≠ (sK0 ◇ sK0) := superpose eq8 eq9 -- forward demodulation 9,8
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq13 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq13 rfl


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
theorem Equation102_implies_Equation1020 (G : Type*) [Magma G] (h : Equation102 G) : Equation1020 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq8


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
theorem Equation102_implies_Equation2644 (G : Type*) [Magma G] (h : Equation102 G) : Equation2644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq12 -- forward demodulation 12,11
  subsumption eq13 eq11


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
theorem Equation102_implies_Equation3050 (G : Type*) [Magma G] (h : Equation102 G) : Equation3050 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq13 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11


@[equational_result]
theorem Equation102_implies_Equation2441 (G : Type*) [Magma G] (h : Equation102 G) : Equation2441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 : sK0 ≠ (sK0 ◇ sK0) := superpose eq8 eq9 -- forward demodulation 9,8
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq13 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq13 rfl


@[equational_result]
theorem Equation102_implies_Equation1223 (G : Type*) [Magma G] (h : Equation102 G) : Equation1223 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq8


@[equational_result]
theorem Equation102_implies_Equation307 (G : Type*) [Magma G] (h : Equation102 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq11


@[equational_result]
theorem Equation102_implies_Equation2847 (G : Type*) [Magma G] (h : Equation102 G) : Equation2847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq13 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11


@[equational_result]
theorem Equation102_implies_Equation375 (G : Type*) [Magma G] (h : Equation102 G) : Equation375 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 rfl


@[equational_result]
theorem Equation102_implies_Equation3319 (G : Type*) [Magma G] (h : Equation102 G) : Equation3319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq13 -- forward demodulation 13,12
  subsumption eq14 rfl


@[equational_result]
theorem Equation102_implies_Equation3456 (G : Type*) [Magma G] (h : Equation102 G) : Equation3456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 : sK0 ≠ (sK0 ◇ sK0) := superpose eq8 eq9 -- forward demodulation 9,8
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq13 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq13 rfl


@[equational_result]
theorem Equation102_implies_Equation4065 (G : Type*) [Magma G] (h : Equation102 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq12 -- forward demodulation 12,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation102_implies_Equation3715 (G : Type*) [Magma G] (h : Equation102 G) : Equation3715 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq13 -- forward demodulation 13,12
  subsumption eq14 rfl


@[equational_result]
theorem Equation102_implies_Equation3722 (G : Type*) [Magma G] (h : Equation102 G) : Equation3722 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq14 rfl


@[equational_result]
theorem Equation102_implies_Equation1832 (G : Type*) [Magma G] (h : Equation102 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq12 -- forward demodulation 12,11
  subsumption eq13 eq11


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
theorem Equation2381_implies_Equation4090 (G : Type*) [Magma G] (h : Equation2381 G) : Equation4090 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X2) ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2 in 12
  have eq17 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq18 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq19 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq17 eq18 -- forward demodulation 18,17
  have eq37 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq50 : sK0 ≠ sK0 := superpose eq37 eq19 -- superposition 19,37, 37 into 19, unify on (0).2 in 37 and (0).2 in 19
  subsumption eq50 rfl


@[equational_result]
theorem Equation2381_implies_Equation2466 (G : Type*) [Magma G] (h : Equation2381 G) : Equation2466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X2) ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2 in 12
  have eq17 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq18 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq21 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.1.2.2 in 9
  have eq82 : sK0 ≠ sK0 := superpose eq21 eq18 -- superposition 18,21, 21 into 18, unify on (0).2 in 21 and (0).2 in 18
  subsumption eq82 rfl


@[equational_result]
theorem Equation2381_implies_Equation4666 (G : Type*) [Magma G] (h : Equation2381 G) : Equation4666 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq28 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq35 : sK1 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq28 eq10 -- backward demodulation 10,28
  subsumption eq35 eq28


@[equational_result]
theorem Equation2381_implies_Equation228 (G : Type*) [Magma G] (h : Equation2381 G) : Equation228 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2381_implies_Equation2649 (G : Type*) [Magma G] (h : Equation2381 G) : Equation2649 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X2) ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2 in 12
  have eq17 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq18 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq21 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.1.2.2 in 9
  have eq91 : sK0 ≠ sK0 := superpose eq21 eq18 -- superposition 18,21, 21 into 18, unify on (0).2 in 21 and (0).2 in 18
  subsumption eq91 rfl


@[equational_result]
theorem Equation2381_implies_Equation2716 (G : Type*) [Magma G] (h : Equation2381 G) : Equation2716 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq28 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq49 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1) = X1 := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).1.1.2.2 in 9
  have eq115 : sK0 ≠ sK0 := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2 in 10
  subsumption eq115 rfl


@[equational_result]
theorem Equation495_implies_Equation583 (G : Type*) [Magma G] (h : Equation495 G) : Equation583 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X3 ◇ X1) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq24 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq22


@[equational_result]
theorem Equation495_implies_Equation549 (G : Type*) [Magma G] (h : Equation495 G) : Equation549 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X3 ◇ X1) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq24 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (X0 ◇ (sK3 ◇ sK0)))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.2 in 10
  subsumption eq24 eq22


@[equational_result]
theorem Equation481_implies_Equation4622 (G : Type*) [Magma G] (h : Equation481 G) : Equation4622 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((X0 ◇ X0) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation481_implies_Equation1426 (G : Type*) [Magma G] (h : Equation481 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq16 (X0 : G) : sK0 ≠ ((X0 ◇ X0) ◇ (sK0 ◇ (X0 ◇ X0))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.1 in 9
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ (X1 ◇ X1))) = X2 := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.2.2 in 8
  have eq26 (X0 : G) : sK0 ≠ (((sK0 ◇ (X0 ◇ X0)) ◇ (sK0 ◇ (X0 ◇ X0))) ◇ (sK0 ◇ (X0 ◇ X0))) := superpose eq8 eq16 -- superposition 16,8, 8 into 16, unify on (0).2 in 8 and (0).2.2 in 16
  subsumption eq26 eq18


@[equational_result]
theorem Equation481_implies_Equation3659 (G : Type*) [Magma G] (h : Equation481 G) : Equation3659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq16 (X0 : G) : (X0 ◇ X0) ≠ ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1 in 9
  subsumption eq16 eq11


@[equational_result]
theorem Equation481_implies_Equation4341 (G : Type*) [Magma G] (h : Equation481 G) : Equation4341 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation481_implies_Equation3677 (G : Type*) [Magma G] (h : Equation481 G) : Equation3677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 eq12


@[equational_result]
theorem Equation481_implies_Equation3684 (G : Type*) [Magma G] (h : Equation481 G) : Equation3684 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 : G) : (X0 ◇ X0) ≠ ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).1 in 10
  have eq32 (X0 : G) : (X0 ◇ X0) ≠ (sK1 ◇ sK1) := superpose eq12 eq20 -- superposition 20,12, 12 into 20, unify on (0).2 in 12 and (0).2 in 20
  subsumption eq32 eq12


@[equational_result]
theorem Equation481_implies_Equation3665 (G : Type*) [Magma G] (h : Equation481 G) : Equation3665 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 eq12


@[equational_result]
theorem Equation481_implies_Equation3662 (G : Type*) [Magma G] (h : Equation481 G) : Equation3662 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 : G) : (X0 ◇ X0) ≠ ((X0 ◇ X0) ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).1 in 10
  have eq31 (X0 : G) : (X0 ◇ X0) ≠ (sK1 ◇ sK1) := superpose eq12 eq20 -- superposition 20,12, 12 into 20, unify on (0).2 in 12 and (0).2 in 20
  subsumption eq31 eq12


@[equational_result]
theorem Equation481_implies_Equation1519 (G : Type*) [Magma G] (h : Equation481 G) : Equation1519 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ (X1 ◇ X1))) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq20 (X0 : G) : sK0 ≠ ((X0 ◇ X0) ◇ (sK0 ◇ (X0 ◇ X0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq20 eq18


@[equational_result]
theorem Equation481_implies_Equation1515 (G : Type*) [Magma G] (h : Equation481 G) : Equation1515 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ (X1 ◇ X1))) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq20 (X0 : G) : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ (X0 ◇ X0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2.2 in 10
  subsumption eq20 eq18


@[equational_result]
theorem Equation481_implies_Equation1429 (G : Type*) [Magma G] (h : Equation481 G) : Equation1429 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ (X1 ◇ X1))) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq20 (X0 : G) : sK0 ≠ ((X0 ◇ X0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq20 eq18


@[equational_result]
theorem Equation481_implies_Equation40 (G : Type*) [Magma G] (h : Equation481 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 eq12


@[equational_result]
theorem Equation481_implies_Equation1523 (G : Type*) [Magma G] (h : Equation481 G) : Equation1523 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ (X1 ◇ X1))) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq20 (X0 : G) : sK0 ≠ ((X0 ◇ X0) ◇ (sK0 ◇ (sK2 ◇ sK2))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq20 eq18


@[equational_result]
theorem Equation2588_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2588 G) : Equation2644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X3) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq17 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1.2 in 8
  have eq43 : sK0 ≠ sK0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2 in 9
  subsumption eq43 rfl


@[equational_result]
theorem Equation2588_implies_Equation231 (G : Type*) [Magma G] (h : Equation2588 G) : Equation231 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2588_implies_Equation2746 (G : Type*) [Magma G] (h : Equation2588 G) : Equation2746 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq18 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq44 : sK0 ≠ sK0 := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq44 rfl


@[equational_result]
theorem Equation2618_implies_Equation2804 (G : Type*) [Magma G] (h : Equation2618 G) : Equation2804 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X5)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation2618_implies_Equation2364 (G : Type*) [Magma G] (h : Equation2618 G) : Equation2364 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X5)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X3 X4 : G) : ((X4 ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X3 : G) : (X3 ◇ X3) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq19 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq19 eq11


@[equational_result]
theorem Equation2618_implies_Equation2787 (G : Type*) [Magma G] (h : Equation2618 G) : Equation2787 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X5)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation2618_implies_Equation3867 (G : Type*) [Magma G] (h : Equation2618 G) : Equation3867 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X5)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X3 X4 : G) : ((X4 ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq15 (X3 : G) : (X3 ◇ X3) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq24 : sK0 ≠ sK0 := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  subsumption eq24 rfl


@[equational_result]
theorem Equation2618_implies_Equation2679 (G : Type*) [Magma G] (h : Equation2618 G) : Equation2679 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X5)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation2618_implies_Equation238 (G : Type*) [Magma G] (h : Equation2618 G) : Equation238 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X5)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation2618_implies_Equation1958 (G : Type*) [Magma G] (h : Equation2618 G) : Equation1958 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X5)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X3 X4 : G) : ((X4 ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X3 : G) : (X3 ◇ X3) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq19 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq19 eq11


@[equational_result]
theorem Equation1043_implies_Equation427 (G : Type*) [Magma G] (h : Equation1043 G) : Equation427 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := mod_symm nh
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
theorem Equation1043_implies_Equation3725 (G : Type*) [Magma G] (h : Equation1043 G) : Equation3725 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2.1 in 11
  have eq21 (X0 X1 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq55 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.2 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.2.1 in 21
  have eq131 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.2.1.2 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq12 eq131 -- forward demodulation 131,12
  have eq341 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.2.1 in 9
  have eq364 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq68 eq341 -- forward demodulation 341,68
  have eq635 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq364 eq10 -- superposition 10,364, 364 into 10, unify on (0).2 in 364 and (0).2 in 10
  subsumption eq635 rfl


@[equational_result]
theorem Equation1043_implies_Equation3661 (G : Type*) [Magma G] (h : Equation1043 G) : Equation3661 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2.1 in 11
  have eq21 (X0 X1 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq55 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.2 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.2.1 in 21
  have eq131 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.2.1.2 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq12 eq131 -- forward demodulation 131,12
  have eq341 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.2.1 in 9
  have eq364 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq68 eq341 -- forward demodulation 341,68
  have eq367 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq364 eq144 -- backward demodulation 144,364
  have eq885 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq367 eq10 -- superposition 10,367, 367 into 10, unify on (0).2 in 367 and (0).2 in 10
  subsumption eq885 rfl


@[equational_result]
theorem Equation1043_implies_Equation1238 (G : Type*) [Magma G] (h : Equation1043 G) : Equation1238 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ X0) ◇ ((X4 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)))) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.1.2 in 11
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.1 in 11
  have eq18 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2.1 in 11
  have eq19 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq21 (X0 X1 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq22 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq23 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := superpose eq22 eq10 -- backward demodulation 10,22
  have eq24 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq22 eq23 -- forward demodulation 23,22
  have eq57 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.2 in 11
  have eq94 (X0 X2 : G) : (X0 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq21 eq15 -- superposition 15,21, 21 into 15, unify on (0).2 in 21 and (0).1.2.2 in 15
  have eq113 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq57 eq21 -- superposition 21,57, 57 into 21, unify on (0).2 in 57 and (0).2.2.1 in 21
  have eq295 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq113 eq17 -- superposition 17,113, 113 into 17, unify on (0).2 in 113 and (0).1 in 17
  have eq319 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq12 eq295 -- forward demodulation 295,12
  have eq436 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq319 eq9 -- superposition 9,319, 319 into 9, unify on (0).2 in 319 and (0).1.2.1 in 9
  have eq463 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq113 eq436 -- forward demodulation 436,113
  have eq480 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq463 eq94 -- backward demodulation 94,463
  have eq663 : sK0 ≠ sK0 := superpose eq480 eq24 -- superposition 24,480, 480 into 24, unify on (0).2 in 480 and (0).2 in 24
  subsumption eq663 rfl


@[equational_result]
theorem Equation1043_implies_Equation3316 (G : Type*) [Magma G] (h : Equation1043 G) : Equation3316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
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
  have eq396 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq380 eq10 -- backward demodulation 10,380
  subsumption eq396 rfl


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
theorem Equation1043_implies_Equation836 (G : Type*) [Magma G] (h : Equation1043 G) : Equation836 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1))) := mod_symm nh
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
  have eq379 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq364 eq10 -- backward demodulation 10,364
  have eq381 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq364 eq70 -- backward demodulation 70,364
  have eq439 : sK0 ≠ sK0 := superpose eq381 eq379 -- superposition 379,381, 381 into 379, unify on (0).2 in 381 and (0).2 in 379
  subsumption eq439 rfl


@[equational_result]
theorem Equation1043_implies_Equation426 (G : Type*) [Magma G] (h : Equation1043 G) : Equation426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ X0) ◇ ((X4 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)))) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.1.2 in 11
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.1 in 11
  have eq18 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2.1 in 11
  have eq21 (X0 X1 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq55 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.2 in 11
  have eq66 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq55 eq10 -- backward demodulation 10,55
  have eq93 (X0 X2 : G) : (X0 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq21 eq15 -- superposition 15,21, 21 into 15, unify on (0).2 in 21 and (0).1.2.2 in 15
  have eq111 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.2.1 in 21
  have eq294 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq111 eq17 -- superposition 17,111, 111 into 17, unify on (0).2 in 111 and (0).1 in 17
  have eq318 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq12 eq294 -- forward demodulation 294,12
  have eq435 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq318 eq9 -- superposition 9,318, 318 into 9, unify on (0).2 in 318 and (0).1.2.1 in 9
  have eq462 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq111 eq435 -- forward demodulation 435,111
  have eq479 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq462 eq93 -- backward demodulation 93,462
  have eq649 : sK0 ≠ sK0 := superpose eq479 eq66 -- superposition 66,479, 479 into 66, unify on (0).2 in 479 and (0).2 in 66
  subsumption eq649 rfl


@[equational_result]
theorem Equation1043_implies_Equation3867 (G : Type*) [Magma G] (h : Equation1043 G) : Equation3867 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
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
  have eq396 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq380 eq10 -- backward demodulation 10,380
  subsumption eq396 rfl


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
theorem Equation1043_implies_Equation819 (G : Type*) [Magma G] (h : Equation1043 G) : Equation819 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2.1 in 11
  have eq21 (X0 X1 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq55 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.2 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.2.1 in 21
  have eq131 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.2.1.2 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq12 eq131 -- forward demodulation 131,12
  have eq341 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.2.1 in 9
  have eq364 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq68 eq341 -- forward demodulation 341,68
  have eq367 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq364 eq144 -- backward demodulation 144,364
  have eq395 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq367 eq10 -- backward demodulation 10,367
  subsumption eq395 eq364


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
  have eq2628 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq1606 eq380 -- superposition 380,1606, 1606 into 380, unify on (0).2 in 1606 and (0).1.2 in 380
  have eq5744 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = X2 := superpose eq2628 eq9 -- superposition 9,2628, 2628 into 9, unify on (0).2 in 2628 and (0).1.2.1 in 9
  have eq5900 : sK0 ≠ sK0 := superpose eq5744 eq10 -- superposition 10,5744, 5744 into 10, unify on (0).2 in 5744 and (0).2 in 10
  subsumption eq5900 rfl


@[equational_result]
theorem Equation1043_implies_Equation3660 (G : Type*) [Magma G] (h : Equation1043 G) : Equation3660 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2.1 in 11
  have eq21 (X0 X1 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq55 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.2 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.2.1 in 21
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.2.1.2 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq341 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.2.1 in 9
  have eq364 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq68 eq341 -- forward demodulation 341,68
  have eq367 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq364 eq144 -- backward demodulation 144,364
  have eq853 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq367 eq10 -- superposition 10,367, 367 into 10, unify on (0).2 in 367 and (0).2 in 10
  subsumption eq853 rfl


@[equational_result]
theorem Equation1043_implies_Equation439 (G : Type*) [Magma G] (h : Equation1043 G) : Equation439 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
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
theorem Equation271_implies_Equation1685 (G : Type*) [Magma G] (h : Equation271 G) : Equation1685 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation271_implies_Equation8 (G : Type*) [Magma G] (h : Equation271 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation271_implies_Equation3253 (G : Type*) [Magma G] (h : Equation271 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 rfl


@[equational_result]
theorem Equation271_implies_Equation3862 (G : Type*) [Magma G] (h : Equation271 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 rfl


@[equational_result]
theorem Equation271_implies_Equation411 (G : Type*) [Magma G] (h : Equation271 G) : Equation411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq11


@[equational_result]
theorem Equation271_implies_Equation1832 (G : Type*) [Magma G] (h : Equation271 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq11


@[equational_result]
theorem Equation271_implies_Equation3319 (G : Type*) [Magma G] (h : Equation271 G) : Equation3319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 rfl


@[equational_result]
theorem Equation1849_implies_Equation203 (G : Type*) [Magma G] (h : Equation1849 G) : Equation203 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1 in 10
  have eq18 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2 in 8
  have eq26 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2.2 in 11
  have eq34 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq26 eq18 -- backward demodulation 18,26
  have eq36 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq26 eq13 -- backward demodulation 13,26
  have eq39 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq26 eq9 -- backward demodulation 9,26
  have eq41 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq10 eq34 -- forward demodulation 34,10
  have eq43 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq26 eq36 -- forward demodulation 36,26
  have eq92 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq43 eq41 -- superposition 41,43, 43 into 41, unify on (0).2 in 43 and (0).2 in 41
  have eq112 : sK0 ≠ sK0 := superpose eq92 eq39 -- superposition 39,92, 92 into 39, unify on (0).2 in 92 and (0).2 in 39
  subsumption eq112 rfl


@[equational_result]
theorem Equation1849_implies_Equation4316 (G : Type*) [Magma G] (h : Equation1849 G) : Equation4316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq27 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq40 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ sK0) := superpose eq27 eq10 -- backward demodulation 10,27
  subsumption eq40 eq27


@[equational_result]
theorem Equation1849_implies_Equation3464 (G : Type*) [Magma G] (h : Equation1849 G) : Equation3464 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq27 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq55 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq27 eq10 -- superposition 10,27, 27 into 10, unify on (0).2 in 27 and (0).2 in 10
  subsumption eq55 rfl


@[equational_result]
theorem Equation1849_implies_Equation1431 (G : Type*) [Magma G] (h : Equation1849 G) : Equation1431 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq27 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq35 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq14 -- backward demodulation 14,27
  have eq40 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq35 -- forward demodulation 35,27
  have eq53 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq27 eq10 -- superposition 10,27, 27 into 10, unify on (0).2 in 27 and (0).2 in 10
  subsumption eq53 eq40


@[equational_result]
theorem Equation1849_implies_Equation2441 (G : Type*) [Magma G] (h : Equation1849 G) : Equation2441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1 in 10
  have eq18 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2 in 8
  have eq26 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2.2 in 11
  have eq33 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq26 eq18 -- backward demodulation 18,26
  have eq36 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq26 eq13 -- backward demodulation 13,26
  have eq39 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq26 eq9 -- backward demodulation 9,26
  have eq40 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq10 eq33 -- forward demodulation 33,10
  have eq43 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq26 eq36 -- forward demodulation 36,26
  have eq92 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq43 eq40 -- superposition 40,43, 43 into 40, unify on (0).2 in 43 and (0).2 in 40
  have eq115 : sK0 ≠ sK0 := superpose eq92 eq39 -- superposition 39,92, 92 into 39, unify on (0).2 in 92 and (0).2 in 39
  subsumption eq115 rfl


@[equational_result]
theorem Equation1849_implies_Equation2238 (G : Type*) [Magma G] (h : Equation1849 G) : Equation2238 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1 in 10
  have eq18 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2 in 8
  have eq26 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2.2 in 11
  have eq34 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq26 eq18 -- backward demodulation 18,26
  have eq36 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq26 eq13 -- backward demodulation 13,26
  have eq39 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq26 eq9 -- backward demodulation 9,26
  have eq41 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq10 eq34 -- forward demodulation 34,10
  have eq43 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq26 eq36 -- forward demodulation 36,26
  have eq44 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq26 eq39 -- forward demodulation 39,26
  have eq93 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq43 eq41 -- superposition 41,43, 43 into 41, unify on (0).2 in 43 and (0).2 in 41
  have eq113 : sK0 ≠ sK0 := superpose eq93 eq44 -- superposition 44,93, 93 into 44, unify on (0).2 in 93 and (0).2 in 44
  subsumption eq113 rfl


@[equational_result]
theorem Equation1849_implies_Equation2456 (G : Type*) [Magma G] (h : Equation1849 G) : Equation2456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq19 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq27 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq35 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq14 -- backward demodulation 14,27
  have eq39 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq27 eq19 -- backward demodulation 19,27
  have eq40 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq27 eq10 -- backward demodulation 10,27
  have eq41 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq35 -- forward demodulation 35,27
  have eq43 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq11 eq39 -- forward demodulation 39,11
  have eq92 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq41 eq43 -- superposition 43,41, 41 into 43, unify on (0).2 in 41 and (0).2 in 43
  have eq115 : sK0 ≠ sK0 := superpose eq92 eq40 -- superposition 40,92, 92 into 40, unify on (0).2 in 92 and (0).2 in 40
  subsumption eq115 rfl


@[equational_result]
theorem Equation1849_implies_Equation1635 (G : Type*) [Magma G] (h : Equation1849 G) : Equation1635 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq19 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq27 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq35 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq14 -- backward demodulation 14,27
  have eq39 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq27 eq19 -- backward demodulation 19,27
  have eq40 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq35 -- forward demodulation 35,27
  have eq42 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq11 eq39 -- forward demodulation 39,11
  have eq50 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq27 eq27 -- superposition 27,27, 27 into 27, unify on (0).2 in 27 and (0).1.2 in 27
  have eq91 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq40 eq42 -- superposition 42,40, 40 into 42, unify on (0).2 in 40 and (0).2 in 42
  have eq174 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq27 eq50 -- superposition 50,27, 27 into 50, unify on (0).2 in 27 and (0).1.1 in 50
  have eq208 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq42 eq174 -- forward demodulation 174,42
  have eq209 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose eq42 eq208 -- forward demodulation 208,42
  have eq210 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose eq91 eq209 -- forward demodulation 209,91
  have eq303 : sK0 ≠ sK0 := superpose eq210 eq10 -- superposition 10,210, 210 into 10, unify on (0).2 in 210 and (0).2 in 10
  subsumption eq303 rfl


@[equational_result]
theorem Equation1849_implies_Equation307 (G : Type*) [Magma G] (h : Equation1849 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq26 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2.2 in 11
  have eq52 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).2 in 9
  subsumption eq52 rfl


@[equational_result]
theorem Equation1849_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1849 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1 in 10
  have eq18 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2 in 8
  have eq26 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2.2 in 11
  have eq34 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq26 eq18 -- backward demodulation 18,26
  have eq36 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq26 eq13 -- backward demodulation 13,26
  have eq40 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq10 eq34 -- forward demodulation 34,10
  have eq42 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq26 eq36 -- forward demodulation 36,26
  have eq91 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq42 eq40 -- superposition 40,42, 42 into 40, unify on (0).2 in 42 and (0).2 in 40
  have eq106 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq91 eq9 -- backward demodulation 9,91
  subsumption eq106 eq91


@[equational_result]
theorem Equation1849_implies_Equation309 (G : Type*) [Magma G] (h : Equation1849 G) : Equation309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq27 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq55 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq27 eq10 -- superposition 10,27, 27 into 10, unify on (0).2 in 27 and (0).1 in 10
  subsumption eq55 rfl


@[equational_result]
theorem Equation1849_implies_Equation2243 (G : Type*) [Magma G] (h : Equation1849 G) : Equation2243 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq19 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq27 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq35 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq14 -- backward demodulation 14,27
  have eq39 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq27 eq19 -- backward demodulation 19,27
  have eq40 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq27 eq10 -- backward demodulation 10,27
  have eq41 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq35 -- forward demodulation 35,27
  have eq43 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq11 eq39 -- forward demodulation 39,11
  have eq44 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq27 eq40 -- forward demodulation 40,27
  have eq93 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq41 eq43 -- superposition 43,41, 41 into 43, unify on (0).2 in 41 and (0).2 in 43
  have eq113 : sK0 ≠ sK0 := superpose eq93 eq44 -- superposition 44,93, 93 into 44, unify on (0).2 in 93 and (0).2 in 44
  subsumption eq113 rfl


@[equational_result]
theorem Equation1849_implies_Equation2476 (G : Type*) [Magma G] (h : Equation1849 G) : Equation2476 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq19 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq27 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq35 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq14 -- backward demodulation 14,27
  have eq39 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq27 eq19 -- backward demodulation 19,27
  have eq40 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq27 eq10 -- backward demodulation 10,27
  have eq41 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq35 -- forward demodulation 35,27
  have eq43 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq11 eq39 -- forward demodulation 39,11
  have eq92 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq41 eq43 -- superposition 43,41, 41 into 43, unify on (0).2 in 41 and (0).2 in 43
  have eq112 : sK0 ≠ sK0 := superpose eq92 eq40 -- superposition 40,92, 92 into 40, unify on (0).2 in 92 and (0).2 in 40
  subsumption eq112 rfl


@[equational_result]
theorem Equation1849_implies_Equation3457 (G : Type*) [Magma G] (h : Equation1849 G) : Equation3457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq27 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq38 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq27 eq12 -- backward demodulation 12,27
  have eq59 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq38 eq10 -- superposition 10,38, 38 into 10, unify on (0).2 in 38 and (0).2 in 10
  subsumption eq59 rfl


@[equational_result]
theorem Equation1849_implies_Equation4128 (G : Type*) [Magma G] (h : Equation1849 G) : Equation4128 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq19 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq27 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq35 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq27 eq19 -- backward demodulation 19,27
  have eq37 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq14 -- backward demodulation 14,27
  have eq41 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq11 eq35 -- forward demodulation 35,11
  have eq43 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq37 -- forward demodulation 37,27
  have eq51 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq27 eq27 -- superposition 27,27, 27 into 27, unify on (0).2 in 27 and (0).1.2 in 27
  have eq92 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq43 eq41 -- superposition 41,43, 43 into 41, unify on (0).2 in 43 and (0).2 in 41
  have eq174 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq51 eq51 -- superposition 51,51, 51 into 51, unify on (0).2 in 51 and (0).1.1 in 51
  have eq205 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq41 eq174 -- forward demodulation 174,41
  have eq206 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq92 eq205 -- forward demodulation 205,92
  have eq207 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq41 eq206 -- forward demodulation 206,41
  have eq208 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq11 eq207 -- forward demodulation 207,11
  have eq255 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq208 eq10 -- superposition 10,208, 208 into 10, unify on (0).2 in 208 and (0).2 in 10
  subsumption eq255 rfl


@[equational_result]
theorem Equation1849_implies_Equation2443 (G : Type*) [Magma G] (h : Equation1849 G) : Equation2443 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq19 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq27 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq34 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq27 eq19 -- backward demodulation 19,27
  have eq37 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq14 -- backward demodulation 14,27
  have eq38 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq27 eq12 -- backward demodulation 12,27
  have eq40 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq11 eq34 -- forward demodulation 34,11
  have eq43 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq37 -- forward demodulation 37,27
  have eq44 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq38 eq10 -- backward demodulation 10,38
  have eq93 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq43 eq40 -- superposition 40,43, 43 into 40, unify on (0).2 in 43 and (0).2 in 40
  have eq113 : sK0 ≠ sK0 := superpose eq93 eq44 -- superposition 44,93, 93 into 44, unify on (0).2 in 93 and (0).2 in 44
  subsumption eq113 rfl


@[equational_result]
theorem Equation1849_implies_Equation1429 (G : Type*) [Magma G] (h : Equation1849 G) : Equation1429 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq27 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq35 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq14 -- backward demodulation 14,27
  have eq40 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq35 -- forward demodulation 35,27
  have eq68 : sK0 ≠ sK0 := superpose eq40 eq10 -- superposition 10,40, 40 into 10, unify on (0).2 in 40 and (0).2 in 10
  subsumption eq68 rfl


@[equational_result]
theorem Equation1849_implies_Equation1428 (G : Type*) [Magma G] (h : Equation1849 G) : Equation1428 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq27 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq35 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq14 -- backward demodulation 14,27
  have eq40 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq27 eq10 -- backward demodulation 10,27
  have eq41 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq35 -- forward demodulation 35,27
  subsumption eq40 eq41


@[equational_result]
theorem Equation1849_implies_Equation1427 (G : Type*) [Magma G] (h : Equation1849 G) : Equation1427 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq27 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq37 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq14 -- backward demodulation 14,27
  have eq43 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq37 -- forward demodulation 37,27
  have eq69 : sK0 ≠ sK0 := superpose eq43 eq10 -- superposition 10,43, 43 into 10, unify on (0).2 in 43 and (0).2 in 10
  subsumption eq69 rfl


@[equational_result]
theorem Equation1849_implies_Equation151 (G : Type*) [Magma G] (h : Equation1849 G) : Equation151 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1 in 10
  have eq26 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2.2 in 11
  have eq36 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq26 eq13 -- backward demodulation 13,26
  have eq42 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq26 eq36 -- forward demodulation 36,26
  have eq68 : sK0 ≠ sK0 := superpose eq42 eq9 -- superposition 9,42, 42 into 9, unify on (0).2 in 42 and (0).2 in 9
  subsumption eq68 rfl


@[equational_result]
theorem Equation1849_implies_Equation1430 (G : Type*) [Magma G] (h : Equation1849 G) : Equation1430 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq27 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq35 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq14 -- backward demodulation 14,27
  have eq40 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq35 -- forward demodulation 35,27
  have eq68 : sK0 ≠ sK0 := superpose eq40 eq10 -- superposition 10,40, 40 into 10, unify on (0).2 in 40 and (0).2 in 10
  subsumption eq68 rfl


@[equational_result]
theorem Equation2415_implies_Equation2753 (G : Type*) [Magma G] (h : Equation2415 G) : Equation2753 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X4 ◇ (X5 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


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
theorem Equation4493_implies_Equation4599 (G : Type*) [Magma G] (h : Equation4493 G) : Equation4599 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 : ((sK0 ◇ sK0) ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X0) = ((X3 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq18 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X2)) = ((X2 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq68 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = ((X3 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq15 eq18 -- superposition 18,15, 15 into 18, unify on (0).2 in 15 and (0).2 in 18
  have eq296 (X2 X3 X4 : G) : (X2 ◇ (X4 ◇ X4)) = (X2 ◇ (X3 ◇ X3)) := superpose eq68 eq68 -- superposition 68,68, 68 into 68, unify on (0).2 in 68 and (0).2 in 68
  have eq562 (X0 : G) : (sK1 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq296 eq12 -- superposition 12,296, 296 into 12, unify on (0).2 in 296 and (0).1 in 12
  subsumption eq562 eq296


@[equational_result]
theorem Equation841_implies_Equation1240 (G : Type*) [Magma G] (h : Equation841 G) : Equation1240 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X4) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq19 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq19 eq12


@[equational_result]
theorem Equation841_implies_Equation1261 (G : Type*) [Magma G] (h : Equation841 G) : Equation1261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ sK3)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X4) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq29 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation841_implies_Equation3726 (G : Type*) [Magma G] (h : Equation841 G) : Equation3726 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X4) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).1.2.1 in 12
  have eq83 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq83 rfl


@[equational_result]
theorem Equation841_implies_Equation1250 (G : Type*) [Magma G] (h : Equation841 G) : Equation1250 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X4) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq29 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation841_implies_Equation1259 (G : Type*) [Magma G] (h : Equation841 G) : Equation1259 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X4) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq29 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation841_implies_Equation1230 (G : Type*) [Magma G] (h : Equation841 G) : Equation1230 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X4) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq25 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq25 rfl


@[equational_result]
theorem Equation841_implies_Equation1260 (G : Type*) [Magma G] (h : Equation841 G) : Equation1260 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X4) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq29 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation1465_implies_Equation1451 (G : Type*) [Magma G] (h : Equation1465 G) : Equation1451 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq47 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation1465_implies_Equation1461 (G : Type*) [Magma G] (h : Equation1465 G) : Equation1461 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq47 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation1465_implies_Equation1441 (G : Type*) [Magma G] (h : Equation1465 G) : Equation1441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq47 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation1465_implies_Equation1457 (G : Type*) [Magma G] (h : Equation1465 G) : Equation1457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq47 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation1465_implies_Equation4360 (G : Type*) [Magma G] (h : Equation1465 G) : Equation4360 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq47 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X2 ◇ (X3 ◇ X0)) := superpose eq14 eq11 -- superposition 11,14, 14 into 11, unify on (0).2 in 14 and (0).2.2.2 in 11
  have eq141 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq47 eq10 -- superposition 10,47, 47 into 10, unify on (0).2 in 47 and (0).2 in 10
  subsumption eq141 eq47


@[equational_result]
theorem Equation1465_implies_Equation1434 (G : Type*) [Magma G] (h : Equation1465 G) : Equation1434 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq50 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1465_implies_Equation1469 (G : Type*) [Magma G] (h : Equation1465 G) : Equation1469 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq47 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq47 rfl


