import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation4568_implies_Equation4516 (G : Type*) [Magma G] (h : Equation4568 G) : Equation4516 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X1 ◇ X2)) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X1)) = (X4 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK2 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq70 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq293 (X1 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ (X3 ◇ X4)) = (X6 ◇ ((X7 ◇ X2) ◇ X1)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1 in 11
  have eq355 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ X2) ◇ X1)) ≠ (X5 ◇ (sK2 ◇ sK2)) := superpose eq11 eq70 -- superposition 70,11, 11 into 70, unify on (0).2 in 11 and (0).2 in 70
  subsumption eq355 eq293


@[equational_result]
theorem Equation4568_implies_Equation4525 (G : Type*) [Magma G] (h : Equation4568 G) : Equation4525 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X1 ◇ X2)) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X1)) = (X4 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK2 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq77 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq293 (X1 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ (X3 ◇ X4)) = (X6 ◇ ((X7 ◇ X2) ◇ X1)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1 in 11
  have eq355 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ X2) ◇ X1)) ≠ (X5 ◇ (sK2 ◇ sK0)) := superpose eq11 eq77 -- superposition 77,11, 11 into 77, unify on (0).2 in 11 and (0).2 in 77
  subsumption eq355 eq293


@[equational_result]
theorem Equation4526_implies_Equation4553 (G : Type*) [Magma G] (h : Equation4526 G) : Equation4553 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK3) ◇ sK1) := mod_symm nh
  have eq14 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X0 ◇ X4)) = ((X2 ◇ (X0 ◇ X1)) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK3) ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq195 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ (X2 ◇ X5)) = ((X1 ◇ (X0 ◇ X4)) ◇ X6) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq218 (X0 X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((X2 ◇ (X0 ◇ (sK2 ◇ sK3))) ◇ X3) := superpose eq14 eq21 -- superposition 21,14, 14 into 21, unify on (0).2 in 14 and (0).2 in 21
  subsumption eq218 eq195


@[equational_result]
theorem Equation4526_implies_Equation4428 (G : Type*) [Magma G] (h : Equation4526 G) : Equation4428 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ sK1) := mod_symm nh
  have eq14 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X0 ◇ X4)) = ((X2 ◇ (X0 ◇ X1)) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK3 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq195 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ (X2 ◇ X5)) = ((X1 ◇ (X0 ◇ X4)) ◇ X6) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq218 (X0 X2 X3 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X2 ◇ (X0 ◇ (sK2 ◇ sK3))) ◇ X3) := superpose eq14 eq21 -- superposition 21,14, 14 into 21, unify on (0).2 in 14 and (0).2 in 21
  subsumption eq218 eq195


@[equational_result]
theorem Equation4526_implies_Equation4549 (G : Type*) [Magma G] (h : Equation4526 G) : Equation4549 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq14 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X0 ◇ X4)) = ((X2 ◇ (X0 ◇ X1)) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK2) ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq195 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ (X2 ◇ X5)) = ((X1 ◇ (X0 ◇ X4)) ◇ X6) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq209 (X0 X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((X2 ◇ (X0 ◇ (sK2 ◇ sK2))) ◇ X3) := superpose eq14 eq21 -- superposition 21,14, 14 into 21, unify on (0).2 in 14 and (0).2 in 21
  subsumption eq209 eq195


@[equational_result]
theorem Equation4526_implies_Equation4569 (G : Type*) [Magma G] (h : Equation4526 G) : Equation4569 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq14 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X0 ◇ X4)) = ((X2 ◇ (X0 ◇ X1)) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK3 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK2) ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq195 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ (X2 ◇ X5)) = ((X1 ◇ (X0 ◇ X4)) ◇ X6) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq213 (X0 X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((X2 ◇ (X0 ◇ (sK3 ◇ sK2))) ◇ X3) := superpose eq14 eq21 -- superposition 21,14, 14 into 21, unify on (0).2 in 14 and (0).2 in 21
  subsumption eq213 eq195


@[equational_result]
theorem Equation4526_implies_Equation4515 (G : Type*) [Magma G] (h : Equation4526 G) : Equation4515 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq14 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X0 ◇ X4)) = ((X2 ◇ (X0 ◇ X1)) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK0 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK2) ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq195 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ (X2 ◇ X5)) = ((X1 ◇ (X0 ◇ X4)) ◇ X6) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq218 (X0 X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((X2 ◇ (X0 ◇ (sK0 ◇ sK2))) ◇ X3) := superpose eq14 eq21 -- superposition 21,14, 14 into 21, unify on (0).2 in 14 and (0).2 in 21
  subsumption eq218 eq195


@[equational_result]
theorem Equation4526_implies_Equation4517 (G : Type*) [Magma G] (h : Equation4526 G) : Equation4517 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK2) ◇ sK3) := mod_symm nh
  have eq14 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X0 ◇ X4)) = ((X2 ◇ (X0 ◇ X1)) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK0 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK2) ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq195 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ (X2 ◇ X5)) = ((X1 ◇ (X0 ◇ X4)) ◇ X6) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq218 (X0 X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((X2 ◇ (X0 ◇ (sK0 ◇ sK2))) ◇ X3) := superpose eq14 eq21 -- superposition 21,14, 14 into 21, unify on (0).2 in 14 and (0).2 in 21
  subsumption eq218 eq195


@[equational_result]
theorem Equation4553_implies_Equation4568 (G : Type*) [Magma G] (h : Equation4553 G) : Equation4568 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X0)) = (X4 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK3)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ X1) ◇ sK1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq72 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ X0)) = ((X3 ◇ (X1 ◇ X2)) ◇ X5) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2.1 in 9
  have eq151 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((X2 ◇ (X0 ◇ X1)) ◇ sK1) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2.1 in 20
  subsumption eq151 eq72


@[equational_result]
theorem Equation4553_implies_Equation4672 (G : Type*) [Magma G] (h : Equation4553 G) : Equation4672 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK1) ◇ sK3) := mod_symm nh
  have eq14 (X0 X2 X3 X4 X5 : G) : (X4 ◇ ((X2 ◇ X3) ◇ X0)) = ((X3 ◇ X5) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq19 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ (X0 ◇ (sK3 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq103 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X6) ◇ X0) = (X5 ◇ ((X3 ◇ X4) ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1.2 in 14
  have eq151 (X0 X2 X3 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ (X2 ◇ (((sK3 ◇ sK0) ◇ X0) ◇ X3)) := superpose eq14 eq19 -- superposition 19,14, 14 into 19, unify on (0).2 in 14 and (0).2 in 19
  subsumption eq151 eq103


@[equational_result]
theorem Equation4553_implies_Equation4652 (G : Type*) [Magma G] (h : Equation4553 G) : Equation4652 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK2 ◇ sK3) ◇ sK3) := mod_symm nh
  have eq14 (X0 X2 X3 X4 X5 : G) : (X4 ◇ ((X2 ◇ X3) ◇ X0)) = ((X3 ◇ X5) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq19 (X0 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (X0 ◇ (sK3 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq103 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X6) ◇ X0) = (X5 ◇ ((X3 ◇ X4) ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1.2 in 14
  have eq151 (X0 X2 X3 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (X2 ◇ (((sK3 ◇ sK2) ◇ X0) ◇ X3)) := superpose eq14 eq19 -- superposition 19,14, 14 into 19, unify on (0).2 in 14 and (0).2 in 19
  subsumption eq151 eq103


@[equational_result]
theorem Equation4553_implies_Equation4676 (G : Type*) [Magma G] (h : Equation4553 G) : Equation4676 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK3) ◇ sK4) := mod_symm nh
  have eq14 (X0 X2 X3 X4 X5 : G) : (X4 ◇ ((X2 ◇ X3) ◇ X0)) = ((X3 ◇ X5) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq19 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ (X0 ◇ (sK4 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq103 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X6) ◇ X0) = (X5 ◇ ((X3 ◇ X4) ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1.2 in 14
  have eq151 (X0 X2 X3 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ (X2 ◇ (((sK4 ◇ sK0) ◇ X0) ◇ X3)) := superpose eq14 eq19 -- superposition 19,14, 14 into 19, unify on (0).2 in 14 and (0).2 in 19
  subsumption eq151 eq103


@[equational_result]
theorem Equation4553_implies_Equation4601 (G : Type*) [Magma G] (h : Equation4553 G) : Equation4601 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq14 (X0 X2 X3 X4 X5 : G) : (X4 ◇ ((X2 ◇ X3) ◇ X0)) = ((X3 ◇ X5) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq19 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ (X0 ◇ (sK0 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq103 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X6) ◇ X0) = (X5 ◇ ((X3 ◇ X4) ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1.2 in 14
  have eq151 (X0 X2 X3 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ (X2 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X3)) := superpose eq14 eq19 -- superposition 19,14, 14 into 19, unify on (0).2 in 14 and (0).2 in 19
  subsumption eq151 eq103


@[equational_result]
theorem Equation4553_implies_Equation4623 (G : Type*) [Magma G] (h : Equation4553 G) : Equation4623 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ sK3) := mod_symm nh
  have eq14 (X0 X2 X3 X4 X5 : G) : (X4 ◇ ((X2 ◇ X3) ◇ X0)) = ((X3 ◇ X5) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq19 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ (X0 ◇ (sK3 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq103 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X6) ◇ X0) = (X5 ◇ ((X3 ◇ X4) ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1.2 in 14
  have eq151 (X0 X2 X3 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ (X2 ◇ (((sK3 ◇ sK2) ◇ X0) ◇ X3)) := superpose eq14 eq19 -- superposition 19,14, 14 into 19, unify on (0).2 in 14 and (0).2 in 19
  subsumption eq151 eq103


@[equational_result]
theorem Equation4553_implies_Equation4628 (G : Type*) [Magma G] (h : Equation4553 G) : Equation4628 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK3) ◇ sK4) := mod_symm nh
  have eq14 (X0 X2 X3 X4 X5 : G) : (X4 ◇ ((X2 ◇ X3) ◇ X0)) = ((X3 ◇ X5) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq19 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ (X0 ◇ (sK4 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq103 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X6) ◇ X0) = (X5 ◇ ((X3 ◇ X4) ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1.2 in 14
  have eq151 (X0 X2 X3 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ (X2 ◇ (((sK4 ◇ sK2) ◇ X0) ◇ X3)) := superpose eq14 eq19 -- superposition 19,14, 14 into 19, unify on (0).2 in 14 and (0).2 in 19
  subsumption eq151 eq103


@[equational_result]
theorem Equation4553_implies_Equation4482 (G : Type*) [Magma G] (h : Equation4553 G) : Equation4482 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X5) ◇ X0) = (X4 ◇ ((X2 ◇ X3) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ X0)) = (((X2 ◇ X3) ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X0)) = (X4 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq77 (X0 X1 : G) : (X1 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq290 (X0 X1 X3 X4 X5 X6 X7 : G) : (X4 ◇ (X3 ◇ X5)) = (X6 ◇ ((X1 ◇ X7) ◇ X0)) := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1 in 11
  have eq354 (X0 X1 X3 X4 X5 : G) : (X5 ◇ (sK1 ◇ sK1)) ≠ (X3 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq11 eq77 -- superposition 77,11, 11 into 77, unify on (0).2 in 11 and (0).1 in 77
  subsumption eq354 eq290


@[equational_result]
theorem Equation4553_implies_Equation4679 (G : Type*) [Magma G] (h : Equation4553 G) : Equation4679 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK1 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq14 (X0 X2 X3 X4 X5 : G) : (X4 ◇ ((X2 ◇ X3) ◇ X0)) = ((X3 ◇ X5) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq19 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq103 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X6) ◇ X0) = (X5 ◇ ((X3 ◇ X4) ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1.2 in 14
  have eq151 (X0 X2 X3 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ (X2 ◇ (((sK0 ◇ sK1) ◇ X0) ◇ X3)) := superpose eq14 eq19 -- superposition 19,14, 14 into 19, unify on (0).2 in 14 and (0).2 in 19
  subsumption eq151 eq103


@[equational_result]
theorem Equation4553_implies_Equation4407 (G : Type*) [Magma G] (h : Equation4553 G) : Equation4407 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X5) ◇ X0) = (X4 ◇ ((X2 ◇ X3) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ X0)) = (((X2 ◇ X3) ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X0)) = (X4 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq77 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK1)) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq290 (X0 X1 X3 X4 X5 X6 X7 : G) : (X4 ◇ (X3 ◇ X5)) = (X6 ◇ ((X1 ◇ X7) ◇ X0)) := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1 in 11
  have eq354 (X0 X1 X3 X4 X5 : G) : (X5 ◇ (sK2 ◇ sK1)) ≠ (X3 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq11 eq77 -- superposition 77,11, 11 into 77, unify on (0).2 in 11 and (0).2 in 77
  subsumption eq354 eq290


@[equational_result]
theorem Equation4553_implies_Equation4473 (G : Type*) [Magma G] (h : Equation4553 G) : Equation4473 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X0)) = (X4 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ X1) ◇ sK1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq73 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ X0)) = ((X3 ◇ (X1 ◇ X2)) ◇ X5) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2.1 in 9
  have eq151 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((X2 ◇ (X0 ◇ X1)) ◇ sK1) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2.1 in 20
  subsumption eq151 eq73


@[equational_result]
theorem Equation4553_implies_Equation4381 (G : Type*) [Magma G] (h : Equation4553 G) : Equation4381 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X5) ◇ X0) = (X4 ◇ ((X2 ◇ X3) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ X0)) = (((X2 ◇ X3) ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X0)) = (X4 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq77 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK0 ◇ sK0)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq290 (X0 X1 X3 X4 X5 X6 X7 : G) : (X4 ◇ (X3 ◇ X5)) = (X6 ◇ ((X1 ◇ X7) ◇ X0)) := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1 in 11
  have eq354 (X0 X1 X3 X4 X5 : G) : (X5 ◇ (sK1 ◇ sK0)) ≠ (X3 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq11 eq77 -- superposition 77,11, 11 into 77, unify on (0).2 in 11 and (0).2 in 77
  subsumption eq354 eq290


@[equational_result]
theorem Equation4553_implies_Equation4686 (G : Type*) [Magma G] (h : Equation4553 G) : Equation4686 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK2 ◇ sK3) ◇ sK0) := mod_symm nh
  have eq14 (X0 X2 X3 X4 X5 : G) : (X4 ◇ ((X2 ◇ X3) ◇ X0)) = ((X3 ◇ X5) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq19 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ (X0 ◇ (sK0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq103 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X6) ◇ X0) = (X5 ◇ ((X3 ◇ X4) ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1.2 in 14
  have eq151 (X0 X2 X3 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ (X2 ◇ (((sK0 ◇ sK2) ◇ X0) ◇ X3)) := superpose eq14 eq19 -- superposition 19,14, 14 into 19, unify on (0).2 in 14 and (0).2 in 19
  subsumption eq151 eq103


@[equational_result]
theorem Equation4553_implies_Equation4598 (G : Type*) [Magma G] (h : Equation4553 G) : Equation4598 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq14 (X0 X2 X3 X4 X5 : G) : (X4 ◇ ((X2 ◇ X3) ◇ X0)) = ((X3 ◇ X5) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq19 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ (X0 ◇ (sK0 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq103 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X6) ◇ X0) = (X5 ◇ ((X3 ◇ X4) ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1.2 in 14
  have eq151 (X0 X2 X3 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ (X2 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X3)) := superpose eq14 eq19 -- superposition 19,14, 14 into 19, unify on (0).2 in 14 and (0).2 in 19
  subsumption eq151 eq103


@[equational_result]
theorem Equation4553_implies_Equation4684 (G : Type*) [Magma G] (h : Equation4553 G) : Equation4684 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK2 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq14 (X0 X2 X3 X4 X5 : G) : (X4 ◇ ((X2 ◇ X3) ◇ X0)) = ((X3 ◇ X5) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq19 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ (X0 ◇ (sK0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq103 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X6) ◇ X0) = (X5 ◇ ((X3 ◇ X4) ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1.2 in 14
  have eq151 (X0 X2 X3 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ (X2 ◇ (((sK0 ◇ sK2) ◇ X0) ◇ X3)) := superpose eq14 eq19 -- superposition 19,14, 14 into 19, unify on (0).2 in 14 and (0).2 in 19
  subsumption eq151 eq103


@[equational_result]
theorem Equation4553_implies_Equation4627 (G : Type*) [Magma G] (h : Equation4553 G) : Equation4627 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK3) ◇ sK3) := mod_symm nh
  have eq14 (X0 X2 X3 X4 X5 : G) : (X4 ◇ ((X2 ◇ X3) ◇ X0)) = ((X3 ◇ X5) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq19 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ (X0 ◇ (sK3 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq103 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X6) ◇ X0) = (X5 ◇ ((X3 ◇ X4) ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1.2 in 14
  have eq151 (X0 X2 X3 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ (X2 ◇ (((sK3 ◇ sK2) ◇ X0) ◇ X3)) := superpose eq14 eq19 -- superposition 19,14, 14 into 19, unify on (0).2 in 14 and (0).2 in 19
  subsumption eq151 eq103


@[equational_result]
theorem Equation4553_implies_Equation4633 (G : Type*) [Magma G] (h : Equation4553 G) : Equation4633 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq14 (X0 X2 X3 X4 X5 : G) : (X4 ◇ ((X2 ◇ X3) ◇ X0)) = ((X3 ◇ X5) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq19 (X0 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (X0 ◇ (sK2 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq103 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X6) ◇ X0) = (X5 ◇ ((X3 ◇ X4) ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1.2 in 14
  have eq151 (X0 X2 X3 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (X2 ◇ (((sK2 ◇ sK0) ◇ X0) ◇ X3)) := superpose eq14 eq19 -- superposition 19,14, 14 into 19, unify on (0).2 in 14 and (0).2 in 19
  subsumption eq151 eq103


@[equational_result]
theorem Equation4553_implies_Equation4493 (G : Type*) [Magma G] (h : Equation4553 G) : Equation4493 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X5) ◇ X0) = (X4 ◇ ((X2 ◇ X3) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ X0)) = (((X2 ◇ X3) ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X0)) = (X4 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq77 (X0 X1 : G) : (X1 ◇ (sK0 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq290 (X0 X1 X3 X4 X5 X6 X7 : G) : (X4 ◇ (X3 ◇ X5)) = (X6 ◇ ((X1 ◇ X7) ◇ X0)) := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1 in 11
  have eq354 (X0 X1 X3 X4 X5 : G) : (X5 ◇ (sK1 ◇ sK1)) ≠ (X3 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq11 eq77 -- superposition 77,11, 11 into 77, unify on (0).2 in 11 and (0).1 in 77
  subsumption eq354 eq290


@[equational_result]
theorem Equation4553_implies_Equation4453 (G : Type*) [Magma G] (h : Equation4553 G) : Equation4453 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq17 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X0)) = (X4 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ X1) ◇ sK1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq72 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ X0)) = ((X3 ◇ (X1 ◇ X2)) ◇ X5) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2.1 in 9
  have eq151 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((X2 ◇ (X0 ◇ X1)) ◇ sK1) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2.1 in 20
  subsumption eq151 eq72


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
theorem Equation3971_implies_Equation3347 (G : Type*) [Magma G] (h : Equation3971 G) : Equation3347 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X3) = ((X3 ◇ (X2 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (((X2 ◇ X3) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (((X2 ◇ X3) ◇ X0) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X0) = ((((X3 ◇ X0) ◇ X1) ◇ X0) ◇ X1) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.1 in 11
  have eq44 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ X1) ◇ X1) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.1 in 28
  have eq52 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X3) = ((X3 ◇ (X2 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) := superpose eq28 eq11 -- superposition 11,28, 28 into 11, unify on (0).2 in 28 and (0).2.1.2 in 11
  have eq56 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X1)) = (((X2 ◇ X3) ◇ X1) ◇ X3) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.1 in 9
  have eq77 (X0 X1 X2 X3 : G) : (((X2 ◇ (X3 ◇ X0)) ◇ X0) ◇ X2) = (X2 ◇ (((X3 ◇ X0) ◇ X1) ◇ X0)) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2 in 15
  have eq93 (X0 X1 X2 X3 : G) : (X2 ◇ (((X3 ◇ X0) ◇ X1) ◇ X0)) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X2 ◇ (((X3 ◇ X0) ◇ X1) ◇ X0)) := superpose eq44 eq93 -- forward demodulation 93,44
  have eq99 (X1 X2 X3 : G) : (X3 ◇ X1) = (((X2 ◇ X3) ◇ X1) ◇ X3) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq100 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X3) = ((X3 ◇ (X2 ◇ X1)) ◇ X1) := superpose eq94 eq52 -- backward demodulation 52,94
  have eq112 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq99 eq94 -- backward demodulation 94,99
  have eq115 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X2) ◇ X0) := superpose eq112 eq9 -- backward demodulation 9,112
  have eq132 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq112 eq10 -- backward demodulation 10,112
  have eq147 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X3) := superpose eq115 eq100 -- forward demodulation 100,115
  have eq148 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq115 eq147 -- forward demodulation 147,115
  have eq149 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X0) ◇ X3) := superpose eq112 eq148 -- forward demodulation 148,112
  have eq175 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ X1)) := superpose eq115 eq115 -- superposition 115,115, 115 into 115, unify on (0).2 in 115 and (0).2.1 in 115
  have eq176 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq112 eq175 -- forward demodulation 175,112
  have eq179 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ X1) := superpose eq115 eq176 -- superposition 176,115, 115 into 176, unify on (0).2 in 115 and (0).2 in 176
  have eq183 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq176 eq179 -- superposition 179,176, 176 into 179, unify on (0).2 in 176 and (0).1 in 179
  have eq195 (X0 : G) : (sK0 ◇ X0) ≠ (sK1 ◇ (sK0 ◇ X0)) := superpose eq179 eq132 -- superposition 132,179, 179 into 132, unify on (0).2 in 179 and (0).1 in 132
  have eq230 (X0 X1 : G) : (sK0 ◇ X0) ≠ (sK1 ◇ X1) := superpose eq179 eq195 -- superposition 195,179, 179 into 195, unify on (0).2 in 179 and (0).2 in 195
  have eq352 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq44 eq149 -- superposition 149,44, 44 into 149, unify on (0).2 in 44 and (0).2 in 149
  have eq410 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (X3 ◇ X1) := superpose eq149 eq183 -- superposition 183,149, 149 into 183, unify on (0).2 in 149 and (0).2 in 183
  have eq500 (X0 X1 : G) : (sK1 ◇ X1) ≠ (X0 ◇ sK0) := superpose eq352 eq230 -- superposition 230,352, 352 into 230, unify on (0).2 in 352 and (0).1 in 230
  subsumption eq500 eq410


@[equational_result]
theorem Equation3971_implies_Equation3939 (G : Type*) [Magma G] (h : Equation3971 G) : Equation3939 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X3) = ((X3 ◇ (X2 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (((X2 ◇ X3) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq28 (X0 X1 X2 X3 : G) : (((X2 ◇ (X3 ◇ X0)) ◇ X0) ◇ (X3 ◇ X0)) = ((X3 ◇ X0) ◇ (((X3 ◇ X0) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X0) = ((((X3 ◇ X0) ◇ X1) ◇ X0) ◇ X1) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.1 in 11
  have eq35 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (((X3 ◇ X0) ◇ X1) ◇ X0)) = ((X0 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq9 eq28 -- forward demodulation 28,9
  have eq37 (X0 X2 X3 : G) : (X3 ◇ X2) = ((((X2 ◇ X0) ◇ X3) ◇ X2) ◇ X3) := superpose eq9 eq29 -- superposition 29,9, 9 into 29, unify on (0).2 in 9 and (0).2.1.1.1 in 29
  have eq45 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ X1) ◇ X1) := superpose eq29 eq29 -- superposition 29,29, 29 into 29, unify on (0).2 in 29 and (0).2.1 in 29
  have eq48 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq29 -- superposition 29,9, 9 into 29, unify on (0).2 in 9 and (0).2 in 29
  have eq57 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X1)) = (((X2 ◇ X3) ◇ X1) ◇ X3) := superpose eq29 eq9 -- superposition 9,29, 29 into 9, unify on (0).2 in 29 and (0).2.1 in 9
  have eq62 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq65 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = ((X2 ◇ X0) ◇ X2) := superpose eq9 eq45 -- superposition 45,9, 9 into 45, unify on (0).2 in 9 and (0).2.1 in 45
  have eq66 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = ((X1 ◇ X0) ◇ X1) := superpose eq11 eq45 -- superposition 45,11, 11 into 45, unify on (0).2 in 11 and (0).2.1 in 45
  have eq67 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq45 eq45 -- superposition 45,45, 45 into 45, unify on (0).2 in 45 and (0).2.1 in 45
  have eq70 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq29 eq45 -- superposition 45,29, 29 into 45, unify on (0).2 in 29 and (0).2 in 45
  have eq79 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq45 eq11 -- superposition 11,45, 45 into 11, unify on (0).2 in 45 and (0).2.1 in 11
  have eq80 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq45 eq9 -- superposition 9,45, 45 into 9, unify on (0).2 in 45 and (0).2.1 in 9
  have eq82 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq67 eq66 -- backward demodulation 66,67
  have eq83 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ X2)) := superpose eq67 eq65 -- backward demodulation 65,67
  have eq86 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq45 eq70 -- forward demodulation 70,45
  have eq87 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = (X2 ◇ X2) := superpose eq86 eq62 -- backward demodulation 62,86
  have eq92 (X0 X1 X2 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq87 eq82 -- backward demodulation 82,87
  have eq93 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ X2) := superpose eq87 eq83 -- backward demodulation 83,87
  have eq98 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq92 eq79 -- forward demodulation 79,92
  have eq100 (X2 X3 : G) : (X3 ◇ X2) = ((X2 ◇ X2) ◇ X3) := superpose eq98 eq37 -- backward demodulation 37,98
  have eq103 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = (X2 ◇ X2) := superpose eq93 eq80 -- forward demodulation 80,93
  have eq110 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X3 ◇ X0)) = ((X3 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq103 eq35 -- backward demodulation 35,103
  have eq114 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X1)) = (X3 ◇ X3) := superpose eq103 eq57 -- backward demodulation 57,103
  have eq121 (X1 X3 : G) : (X3 ◇ X3) = (X3 ◇ (X1 ◇ X1)) := superpose eq103 eq114 -- forward demodulation 114,103
  have eq152 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((X2 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq87 eq9 -- superposition 9,87, 87 into 9, unify on (0).2 in 87 and (0).2.1.2 in 9
  have eq180 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X1) := superpose eq100 eq100 -- superposition 100,100, 100 into 100, unify on (0).2 in 100 and (0).2.1 in 100
  have eq199 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq45 eq180 -- forward demodulation 180,45
  have eq200 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq100 eq199 -- forward demodulation 199,100
  have eq207 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq200 eq152 -- backward demodulation 152,200
  have eq211 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X3 ◇ X0)) = ((X3 ◇ X0) ◇ X0) := superpose eq200 eq110 -- backward demodulation 110,200
  have eq220 (X0 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq45 eq211 -- forward demodulation 211,45
  have eq242 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X1 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq11 eq220 -- superposition 220,11, 11 into 220, unify on (0).2 in 11 and (0).2.1 in 220
  have eq245 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq100 eq220 -- superposition 220,100, 100 into 220, unify on (0).2 in 100 and (0).2.1 in 220
  have eq272 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq220 eq11 -- superposition 11,220, 220 into 11, unify on (0).2 in 220 and (0).2.1.2 in 11
  have eq278 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq200 eq245 -- forward demodulation 245,200
  have eq279 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq100 eq278 -- forward demodulation 278,100
  have eq280 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X2) := superpose eq279 eq207 -- backward demodulation 207,279
  have eq303 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq280 eq242 -- backward demodulation 242,280
  have eq326 (X0 X1 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X1) ◇ X3) := superpose eq303 eq272 -- forward demodulation 272,303
  have eq337 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq121 eq121 -- superposition 121,121, 121 into 121, unify on (0).2 in 121 and (0).2.2 in 121
  have eq369 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq200 eq337 -- forward demodulation 337,200
  have eq370 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq369 eq10 -- backward demodulation 10,369
  subsumption eq370 eq326


@[equational_result]
theorem Equation3971_implies_Equation3887 (G : Type*) [Magma G] (h : Equation3971 G) : Equation3887 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X3) = ((X3 ◇ (X2 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (((X2 ◇ X3) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq28 (X0 X1 X2 X3 : G) : (((X2 ◇ (X3 ◇ X0)) ◇ X0) ◇ (X3 ◇ X0)) = ((X3 ◇ X0) ◇ (((X3 ◇ X0) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X0) = ((((X3 ◇ X0) ◇ X1) ◇ X0) ◇ X1) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.1 in 11
  have eq32 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4) = ((X4 ◇ (((X3 ◇ X0) ◇ X1) ◇ X0)) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.2 in 9
  have eq35 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (((X3 ◇ X0) ◇ X1) ◇ X0)) = ((X0 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq9 eq28 -- forward demodulation 28,9
  have eq37 (X0 X2 X3 : G) : (X3 ◇ X2) = ((((X2 ◇ X0) ◇ X3) ◇ X2) ◇ X3) := superpose eq9 eq29 -- superposition 29,9, 9 into 29, unify on (0).2 in 9 and (0).2.1.1.1 in 29
  have eq45 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ X1) ◇ X1) := superpose eq29 eq29 -- superposition 29,29, 29 into 29, unify on (0).2 in 29 and (0).2.1 in 29
  have eq48 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq29 -- superposition 29,9, 9 into 29, unify on (0).2 in 9 and (0).2 in 29
  have eq62 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq65 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = ((X2 ◇ X0) ◇ X2) := superpose eq9 eq45 -- superposition 45,9, 9 into 45, unify on (0).2 in 9 and (0).2.1 in 45
  have eq66 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = ((X1 ◇ X0) ◇ X1) := superpose eq11 eq45 -- superposition 45,11, 11 into 45, unify on (0).2 in 11 and (0).2.1 in 45
  have eq67 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq45 eq45 -- superposition 45,45, 45 into 45, unify on (0).2 in 45 and (0).2.1 in 45
  have eq70 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq29 eq45 -- superposition 45,29, 29 into 45, unify on (0).2 in 29 and (0).2 in 45
  have eq79 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq45 eq11 -- superposition 11,45, 45 into 11, unify on (0).2 in 45 and (0).2.1 in 11
  have eq80 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq45 eq9 -- superposition 9,45, 45 into 9, unify on (0).2 in 45 and (0).2.1 in 9
  have eq82 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq67 eq66 -- backward demodulation 66,67
  have eq83 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ X2)) := superpose eq67 eq65 -- backward demodulation 65,67
  have eq86 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ X1) := superpose eq45 eq70 -- forward demodulation 70,45
  have eq87 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = (X2 ◇ X2) := superpose eq86 eq62 -- backward demodulation 62,86
  have eq89 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq86 eq10 -- backward demodulation 10,86
  have eq93 (X0 X1 X2 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq87 eq82 -- backward demodulation 82,87
  have eq94 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ X2) := superpose eq87 eq83 -- backward demodulation 83,87
  have eq99 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq93 eq79 -- forward demodulation 79,93
  have eq101 (X2 X3 : G) : (X3 ◇ X2) = ((X2 ◇ X2) ◇ X3) := superpose eq99 eq37 -- backward demodulation 37,99
  have eq104 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = (X2 ◇ X2) := superpose eq94 eq80 -- forward demodulation 80,94
  have eq110 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4) = ((X4 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := superpose eq104 eq32 -- backward demodulation 32,104
  have eq111 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X3 ◇ X0)) = ((X3 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq104 eq35 -- backward demodulation 35,104
  have eq132 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((X2 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq87 eq9 -- superposition 9,87, 87 into 9, unify on (0).2 in 87 and (0).2.1.2 in 9
  have eq154 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X1) := superpose eq101 eq101 -- superposition 101,101, 101 into 101, unify on (0).2 in 101 and (0).2.1 in 101
  have eq169 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq45 eq154 -- forward demodulation 154,45
  have eq170 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq101 eq169 -- forward demodulation 169,101
  have eq172 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4) = ((X4 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := superpose eq170 eq110 -- backward demodulation 110,170
  have eq174 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq170 eq132 -- backward demodulation 132,170
  have eq178 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X3 ◇ X0)) = ((X3 ◇ X0) ◇ X0) := superpose eq170 eq111 -- backward demodulation 111,170
  have eq181 (X0 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq45 eq178 -- forward demodulation 178,45
  have eq197 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X1 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq11 eq181 -- superposition 181,11, 11 into 181, unify on (0).2 in 11 and (0).2.1 in 181
  have eq200 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq101 eq181 -- superposition 181,101, 101 into 181, unify on (0).2 in 101 and (0).2.1 in 181
  have eq223 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq181 eq11 -- superposition 11,181, 181 into 11, unify on (0).2 in 181 and (0).2.1.2 in 11
  have eq228 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq170 eq200 -- forward demodulation 200,170
  have eq229 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq101 eq228 -- forward demodulation 228,101
  have eq230 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X2) := superpose eq229 eq174 -- backward demodulation 174,229
  have eq243 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4) = (X4 ◇ X0) := superpose eq230 eq172 -- backward demodulation 172,230
  have eq245 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq230 eq197 -- backward demodulation 197,230
  have eq263 (X0 X1 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X1) ◇ X3) := superpose eq245 eq223 -- forward demodulation 223,245
  have eq396 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = ((X2 ◇ X3) ◇ (X0 ◇ X2)) := superpose eq263 eq181 -- superposition 181,263, 263 into 181, unify on (0).2 in 263 and (0).2.2 in 181
  have eq421 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq181 eq396 -- forward demodulation 396,181
  have eq434 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X4) = (X4 ◇ X0) := superpose eq421 eq243 -- backward demodulation 243,421
  have eq441 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X4) = (X4 ◇ X0) := superpose eq421 eq434 -- forward demodulation 434,421
  have eq458 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ X2) := superpose eq101 eq441 -- superposition 441,101, 101 into 441, unify on (0).2 in 101 and (0).1 in 441
  have eq480 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq441 eq89 -- superposition 89,441, 441 into 89, unify on (0).2 in 441 and (0).2 in 89
  subsumption eq480 eq458


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
theorem Equation4195_implies_Equation4305 (G : Type*) [Magma G] (h : Equation4195 G) : Equation4305 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X0) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X3) = (((X1 ◇ X2) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq21 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq15 eq14 -- backward demodulation 14,15
  have eq22 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ sK2) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq23 (X1 X2 : G) : (X1 ◇ X1) = (X1 ◇ (X1 ◇ X2)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).1.2 in 15
  have eq25 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.2 in 15
  have eq27 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (((X0 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).2.1.1 in 9
  have eq29 : (sK2 ◇ sK2) ≠ (sK0 ◇ sK0) := superpose eq23 eq22 -- backward demodulation 22,23
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).1.1 in 21
  have eq37 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq21 eq9 -- superposition 9,21, 21 into 9, unify on (0).2 in 21 and (0).2.1 in 9
  have eq42 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq37 eq27 -- backward demodulation 27,37
  have eq45 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ X1) := superpose eq42 eq25 -- backward demodulation 25,42
  have eq46 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq42 eq33 -- backward demodulation 33,42
  have eq47 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq37 eq45 -- forward demodulation 45,37
  have eq48 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq47 eq46 -- forward demodulation 46,47
  have eq49 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq52 (X1 X2 X3 : G) : (X1 ◇ X3) = ((X2 ◇ X3) ◇ X1) := superpose eq49 eq11 -- backward demodulation 11,49
  have eq55 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X0) ◇ X2) := superpose eq12 eq52 -- superposition 52,12, 12 into 52, unify on (0).2 in 12 and (0).2.1 in 52
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq15 eq52 -- superposition 52,15, 15 into 52, unify on (0).2 in 15 and (0).2.1 in 52
  have eq59 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ X1) := superpose eq12 eq52 -- superposition 52,12, 12 into 52, unify on (0).2 in 12 and (0).2 in 52
  have eq68 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq49 eq58 -- forward demodulation 58,49
  have eq75 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X1) := superpose eq52 eq59 -- superposition 59,52, 52 into 59, unify on (0).2 in 52 and (0).2 in 59
  have eq77 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X0 ◇ X0) ◇ X2) := superpose eq59 eq52 -- superposition 52,59, 59 into 52, unify on (0).2 in 59 and (0).2.1 in 52
  have eq87 (X0 : G) : (sK0 ◇ sK0) ≠ (sK2 ◇ X0) := superpose eq59 eq29 -- superposition 29,59, 59 into 29, unify on (0).2 in 59 and (0).1 in 29
  have eq88 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X0) := superpose eq12 eq75 -- forward demodulation 75,12
  have eq226 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X2) := superpose eq55 eq49 -- superposition 49,55, 55 into 49, unify on (0).2 in 55 and (0).2 in 49
  have eq299 (X1 : G) : (sK0 ◇ sK0) ≠ (X1 ◇ sK2) := superpose eq68 eq87 -- superposition 87,68, 68 into 87, unify on (0).2 in 68 and (0).2 in 87
  have eq487 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X0) := superpose eq77 eq88 -- superposition 88,77, 77 into 88, unify on (0).2 in 77 and (0).1 in 88
  have eq704 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq226 eq226 -- superposition 226,226, 226 into 226, unify on (0).2 in 226 and (0).1 in 226
  have eq967 (X0 X1 : G) : (X0 ◇ X0) ≠ (X1 ◇ sK2) := superpose eq487 eq299 -- superposition 299,487, 487 into 299, unify on (0).2 in 487 and (0).1 in 299
  subsumption eq967 eq704


@[equational_result]
theorem Equation4195_implies_Equation4364 (G : Type*) [Magma G] (h : Equation4195 G) : Equation4364 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X0) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X3) = (((X1 ◇ X2) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq21 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq15 eq14 -- backward demodulation 14,15
  have eq23 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.1.1 in 11
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq28 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq33 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq12 eq25 -- forward demodulation 25,12
  have eq42 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (((X0 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).2.1.1 in 9
  have eq51 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq12 eq21 -- superposition 21,12, 12 into 21, unify on (0).2 in 12 and (0).1.1 in 21
  have eq56 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq21 eq9 -- superposition 9,21, 21 into 9, unify on (0).2 in 21 and (0).2.1 in 9
  have eq61 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq33 eq51 -- forward demodulation 51,33
  have eq66 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq56 eq42 -- backward demodulation 42,56
  have eq69 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) := superpose eq9 eq28 -- superposition 28,9, 9 into 28, unify on (0).2 in 9 and (0).2.2 in 28
  have eq82 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq66 eq69 -- forward demodulation 69,66
  have eq83 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq61 eq82 -- forward demodulation 82,61
  have eq84 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq33 eq83 -- forward demodulation 83,33
  have eq91 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X0) := superpose eq84 eq23 -- backward demodulation 23,84
  have eq94 : (sK1 ◇ (sK2 ◇ sK0)) ≠ (sK2 ◇ sK1) := superpose eq84 eq10 -- backward demodulation 10,84
  have eq97 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X2) ◇ X0) := superpose eq91 eq9 -- backward demodulation 9,91
  have eq104 : (sK2 ◇ sK1) ≠ (sK0 ◇ sK2) := superpose eq84 eq94 -- forward demodulation 94,84
  have eq126 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq12 eq97 -- superposition 97,12, 12 into 97, unify on (0).2 in 12 and (0).2 in 97
  have eq145 : (sK2 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq126 eq104 -- backward demodulation 104,126
  have eq282 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X0) := superpose eq97 eq91 -- superposition 91,97, 97 into 91, unify on (0).2 in 97 and (0).1 in 91
  have eq373 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq282 eq282 -- superposition 282,282, 282 into 282, unify on (0).2 in 282 and (0).1 in 282
  have eq413 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK2) := superpose eq282 eq145 -- superposition 145,282, 282 into 145, unify on (0).2 in 282 and (0).1 in 145
  subsumption eq413 eq373


@[equational_result]
theorem Equation4195_implies_Equation4192 (G : Type*) [Magma G] (h : Equation4195 G) : Equation4192 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X0) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X3) = (((X1 ◇ X2) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq14 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = ((X1 ◇ X2) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq16 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq20 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X1 ◇ (X2 ◇ X1)) := superpose eq15 eq14 -- backward demodulation 14,15
  have eq21 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X1 ◇ X1) := superpose eq16 eq20 -- backward demodulation 20,16
  have eq22 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq16 eq15 -- backward demodulation 15,16
  have eq27 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (((X0 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.1.1 in 9
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq12 eq36 -- forward demodulation 36,12
  have eq52 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq12 eq22 -- superposition 22,12, 12 into 22, unify on (0).2 in 12 and (0).1.1 in 22
  have eq61 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq22 eq9 -- superposition 9,22, 22 into 9, unify on (0).2 in 22 and (0).2.1 in 9
  have eq62 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq46 eq52 -- forward demodulation 52,46
  have eq69 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq61 eq27 -- backward demodulation 27,61
  have eq74 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq16 eq21 -- superposition 21,16, 16 into 21, unify on (0).2 in 16 and (0).1.2.1 in 21
  have eq89 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq61 eq74 -- forward demodulation 74,61
  have eq90 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq62 eq89 -- forward demodulation 89,62
  have eq91 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose eq90 eq69 -- backward demodulation 69,90
  have eq96 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq91 eq9 -- backward demodulation 9,91
  have eq117 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq22 eq96 -- superposition 96,22, 22 into 96, unify on (0).2 in 22 and (0).2 in 96
  have eq121 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq117 eq13 -- backward demodulation 13,117
  subsumption eq121 eq91


@[equational_result]
theorem Equation4195_implies_Equation3348 (G : Type*) [Magma G] (h : Equation4195 G) : Equation3348 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X0) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X3) = (((X1 ◇ X2) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = ((X1 ◇ X2) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq19 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X1 ◇ (X2 ◇ X1)) := superpose eq14 eq13 -- backward demodulation 13,14
  have eq20 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X1 ◇ X1) := superpose eq15 eq19 -- backward demodulation 19,15
  have eq21 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq15 eq14 -- backward demodulation 14,15
  have eq22 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq27 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (((X0 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).2.1.1 in 9
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq12 eq36 -- forward demodulation 36,12
  have eq52 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq12 eq21 -- superposition 21,12, 12 into 21, unify on (0).2 in 12 and (0).1.1 in 21
  have eq57 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq21 eq9 -- superposition 9,21, 21 into 9, unify on (0).2 in 21 and (0).2.1 in 9
  have eq62 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq46 eq52 -- forward demodulation 52,46
  have eq67 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq57 eq27 -- backward demodulation 27,57
  have eq74 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.2.1 in 20
  have eq89 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq57 eq74 -- forward demodulation 74,57
  have eq90 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq62 eq89 -- forward demodulation 89,62
  have eq91 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose eq90 eq67 -- backward demodulation 67,90
  have eq96 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq91 eq9 -- backward demodulation 9,91
  have eq97 (X1 X2 X3 : G) : (X1 ◇ X3) = ((X2 ◇ X3) ◇ X1) := superpose eq91 eq11 -- backward demodulation 11,91
  have eq114 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq96 eq96 -- superposition 96,96, 96 into 96, unify on (0).2 in 96 and (0).1 in 96
  have eq117 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq21 eq96 -- superposition 96,21, 21 into 96, unify on (0).2 in 21 and (0).2 in 96
  have eq121 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq117 eq22 -- backward demodulation 22,117
  have eq123 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq117 eq117 -- superposition 117,117, 117 into 117, unify on (0).2 in 117 and (0).2 in 117
  have eq128 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq117 eq121 -- superposition 121,117, 117 into 121, unify on (0).2 in 117 and (0).2 in 121
  have eq159 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ X0) := superpose eq117 eq128 -- superposition 128,117, 117 into 128, unify on (0).2 in 117 and (0).2 in 128
  have eq168 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq97 eq114 -- superposition 114,97, 97 into 114, unify on (0).2 in 97 and (0).2 in 114
  have eq336 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq97 eq168 -- superposition 168,97, 97 into 168, unify on (0).2 in 97 and (0).2 in 168
  have eq594 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X1) := superpose eq123 eq336 -- superposition 336,123, 123 into 336, unify on (0).2 in 123 and (0).1 in 336
  have eq633 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ X0) := superpose eq336 eq159 -- superposition 159,336, 336 into 159, unify on (0).2 in 336 and (0).2 in 159
  subsumption eq633 eq594


@[equational_result]
theorem Equation4195_implies_Equation4104 (G : Type*) [Magma G] (h : Equation4195 G) : Equation4104 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X0) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X3) = (((X1 ◇ X2) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq19 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X1 ◇ (X2 ◇ X1)) := superpose eq14 eq13 -- backward demodulation 13,14
  have eq20 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq21 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X1 ◇ X1) := superpose eq15 eq19 -- backward demodulation 19,15
  have eq22 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq15 eq14 -- backward demodulation 14,15
  have eq23 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq15 eq20 -- backward demodulation 20,15
  have eq28 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (((X0 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).2.1.1 in 9
  have eq37 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq47 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq53 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq12 eq22 -- superposition 22,12, 12 into 22, unify on (0).2 in 12 and (0).1.1 in 22
  have eq58 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq22 eq9 -- superposition 9,22, 22 into 9, unify on (0).2 in 22 and (0).2.1 in 9
  have eq63 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq47 eq53 -- forward demodulation 53,47
  have eq68 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq58 eq28 -- backward demodulation 28,58
  have eq75 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq15 eq21 -- superposition 21,15, 15 into 21, unify on (0).2 in 15 and (0).1.2.1 in 21
  have eq90 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq58 eq75 -- forward demodulation 75,58
  have eq91 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq63 eq90 -- forward demodulation 90,63
  have eq92 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose eq91 eq68 -- backward demodulation 68,91
  have eq97 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq92 eq9 -- backward demodulation 9,92
  have eq98 (X1 X2 X3 : G) : (X1 ◇ X3) = ((X2 ◇ X3) ◇ X1) := superpose eq92 eq11 -- backward demodulation 11,92
  have eq118 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq22 eq97 -- superposition 97,22, 22 into 97, unify on (0).2 in 22 and (0).2 in 97
  have eq133 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK1) := superpose eq98 eq23 -- superposition 23,98, 98 into 23, unify on (0).2 in 98 and (0).2 in 23
  subsumption eq133 eq118


@[equational_result]
theorem Equation4195_implies_Equation3878 (G : Type*) [Magma G] (h : Equation4195 G) : Equation3878 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X0) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X3) = (((X1 ◇ X2) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq21 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq15 eq14 -- backward demodulation 14,15
  have eq22 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq23 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.1.1 in 11
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq28 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq33 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq12 eq25 -- forward demodulation 25,12
  have eq42 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (((X0 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).2.1.1 in 9
  have eq51 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq12 eq21 -- superposition 21,12, 12 into 21, unify on (0).2 in 12 and (0).1.1 in 21
  have eq56 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq21 eq9 -- superposition 9,21, 21 into 9, unify on (0).2 in 21 and (0).2.1 in 9
  have eq62 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq33 eq51 -- forward demodulation 51,33
  have eq67 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq56 eq42 -- backward demodulation 42,56
  have eq70 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) := superpose eq9 eq28 -- superposition 28,9, 9 into 28, unify on (0).2 in 9 and (0).2.2 in 28
  have eq83 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq67 eq70 -- forward demodulation 70,67
  have eq84 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq62 eq83 -- forward demodulation 83,62
  have eq85 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq33 eq84 -- forward demodulation 84,33
  have eq90 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (X2 ◇ (X0 ◇ X1)) := superpose eq85 eq22 -- backward demodulation 22,85
  have eq92 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X0) := superpose eq85 eq23 -- backward demodulation 23,85
  have eq95 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq85 eq10 -- backward demodulation 10,85
  have eq96 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ X3) := superpose eq85 eq90 -- forward demodulation 90,85
  have eq104 (X0 X1 X3 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X3) := superpose eq92 eq96 -- backward demodulation 96,92
  subsumption eq95 eq104


@[equational_result]
theorem Equation3806_implies_Equation4080 (G : Type*) [Magma G] (h : Equation3806 G) : Equation4080 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X1) ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq18 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq30 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X2))) = ((X4 ◇ (X3 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq33 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X2 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq51 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X1)) = (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X2))) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.2 in 17
  have eq92 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) = (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X2))) := superpose eq18 eq51 -- forward demodulation 51,18
  have eq93 (X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) = ((X4 ◇ (X3 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X1)) := superpose eq92 eq30 -- backward demodulation 30,92
  have eq134 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq12 eq33 -- superposition 33,12, 12 into 33, unify on (0).2 in 12 and (0).2 in 33
  have eq152 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq134 -- forward demodulation 134,9
  have eq159 (X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X3) = ((X4 ◇ (X3 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X1)) := superpose eq152 eq93 -- backward demodulation 93,152
  have eq183 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X1 ◇ X2) ◇ (X2 ◇ X1)) := superpose eq9 eq152 -- superposition 152,9, 9 into 152, unify on (0).2 in 9 and (0).2.2 in 152
  have eq188 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq152 eq152 -- superposition 152,152, 152 into 152, unify on (0).2 in 152 and (0).2.2 in 152
  have eq201 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq183 -- forward demodulation 183,9
  have eq202 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) := superpose eq201 eq12 -- backward demodulation 12,201
  have eq224 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq188 -- forward demodulation 188,9
  have eq225 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq224 eq10 -- backward demodulation 10,224
  have eq244 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq224 eq225 -- superposition 225,224, 224 into 225, unify on (0).2 in 224 and (0).2 in 225
  have eq257 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X3 ◇ (X4 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X1)) := superpose eq9 eq202 -- superposition 202,9, 9 into 202, unify on (0).2 in 9 and (0).2.2 in 202
  have eq271 (X1 X2 X3 X4 : G) : (X1 ◇ X2) = ((X3 ◇ (X4 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X1)) := superpose eq201 eq257 -- forward demodulation 257,201
  have eq272 (X1 X2 X3 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X3) := superpose eq271 eq159 -- backward demodulation 159,271
  have eq323 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq272 -- superposition 272,9, 9 into 272, unify on (0).2 in 9 and (0).2 in 272
  have eq386 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq323 eq244 -- superposition 244,323, 323 into 244, unify on (0).2 in 323 and (0).2 in 244
  subsumption eq386 eq323


@[equational_result]
theorem Equation3806_implies_Equation4195 (G : Type*) [Magma G] (h : Equation3806 G) : Equation4195 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X1) ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq18 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq30 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X2))) = ((X4 ◇ (X3 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq33 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X2 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq51 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X1)) = (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X2))) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.2 in 17
  have eq92 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) = (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X2))) := superpose eq18 eq51 -- forward demodulation 51,18
  have eq93 (X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) = ((X4 ◇ (X3 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X1)) := superpose eq92 eq30 -- backward demodulation 30,92
  have eq134 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq12 eq33 -- superposition 33,12, 12 into 33, unify on (0).2 in 12 and (0).2 in 33
  have eq152 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq134 -- forward demodulation 134,9
  have eq159 (X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X3) = ((X4 ◇ (X3 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X1)) := superpose eq152 eq93 -- backward demodulation 93,152
  have eq183 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X1 ◇ X2) ◇ (X2 ◇ X1)) := superpose eq9 eq152 -- superposition 152,9, 9 into 152, unify on (0).2 in 9 and (0).2.2 in 152
  have eq201 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq183 -- forward demodulation 183,9
  have eq202 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) := superpose eq201 eq12 -- backward demodulation 12,201
  have eq242 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X3 ◇ (X4 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X1)) := superpose eq9 eq202 -- superposition 202,9, 9 into 202, unify on (0).2 in 9 and (0).2.2 in 202
  have eq252 (X1 X2 X3 X4 : G) : (X1 ◇ X2) = ((X3 ◇ (X4 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X1)) := superpose eq201 eq242 -- forward demodulation 242,201
  have eq253 (X1 X2 X3 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X3) := superpose eq252 eq159 -- backward demodulation 159,252
  have eq254 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq253 eq11 -- backward demodulation 11,253
  have eq266 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK0) ◇ sK0) := superpose eq253 eq10 -- backward demodulation 10,253
  have eq267 (X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq254 -- forward demodulation 254,9
  have eq300 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X3 ◇ X2) := superpose eq267 eq253 -- superposition 253,267, 267 into 253, unify on (0).2 in 267 and (0).2 in 253
  have eq302 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK0) := superpose eq253 eq266 -- superposition 266,253, 253 into 266, unify on (0).2 in 253 and (0).2 in 266
  subsumption eq302 eq300


@[equational_result]
theorem Equation3565_implies_Equation3738 (G : Type*) [Magma G] (h : Equation3565 G) : Equation3738 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X0) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (X3 ◇ ((X2 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq18 (X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X4))) = ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq24 (X0 X2 X3 X4 : G) : (((X3 ◇ X0) ◇ X0) ◇ X4) = (X4 ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2.2 in 13
  have eq27 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq28 (X0 X2 X3 X4 : G) : (((X3 ◇ X0) ◇ X0) ◇ X4) = (X4 ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.2 in 13
  have eq42 (X0 X3 X4 : G) : (((X3 ◇ X0) ◇ X0) ◇ X4) = (X0 ◇ X4) := superpose eq9 eq28 -- forward demodulation 28,9
  have eq43 (X0 X2 X4 : G) : (X4 ◇ (X0 ◇ (X2 ◇ X0))) = (X0 ◇ X4) := superpose eq42 eq24 -- backward demodulation 24,42
  have eq46 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ (X2 ◇ X0))) = (X2 ◇ X3) := superpose eq42 eq13 -- backward demodulation 13,42
  have eq47 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ X3) := superpose eq42 eq27 -- backward demodulation 27,42
  have eq53 (X1 X2 X3 : G) : (X1 ◇ X3) = ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) := superpose eq46 eq18 -- backward demodulation 18,46
  have eq58 (X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X1) ◇ X3) := superpose eq46 eq53 -- forward demodulation 53,46
  have eq60 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ X1) ◇ X3) := superpose eq43 eq47 -- forward demodulation 47,43
  have eq61 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq60 eq9 -- backward demodulation 9,60
  have eq98 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := superpose eq61 eq58 -- superposition 58,61, 61 into 58, unify on (0).2 in 61 and (0).2 in 58
  have eq101 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq61 eq98 -- forward demodulation 98,61
  have eq103 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose eq61 eq60 -- superposition 60,61, 61 into 60, unify on (0).2 in 61 and (0).2.1 in 60
  have eq111 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose eq58 eq103 -- forward demodulation 103,58
  have eq209 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq61 eq101 -- superposition 101,61, 61 into 101, unify on (0).2 in 61 and (0).2 in 101
  have eq291 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X2) := superpose eq60 eq111 -- superposition 111,60, 60 into 111, unify on (0).2 in 60 and (0).2 in 111
  have eq329 (X0 X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ X0) := superpose eq209 eq291 -- superposition 291,209, 209 into 291, unify on (0).2 in 209 and (0).1 in 291
  have eq608 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq329 eq329 -- superposition 329,329, 329 into 329, unify on (0).2 in 329 and (0).1 in 329
  have eq662 (X0 : G) : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK3) ◇ X0) := superpose eq329 eq10 -- superposition 10,329, 329 into 10, unify on (0).2 in 329 and (0).2 in 10
  subsumption eq662 eq608


@[equational_result]
theorem Equation3565_implies_Equation4369 (G : Type*) [Magma G] (h : Equation3565 G) : Equation4369 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X0) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (X3 ◇ ((X2 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ X4))) = (((X2 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq18 (X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X4))) = ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq24 (X0 X2 X3 X4 : G) : (((X3 ◇ X0) ◇ X0) ◇ X4) = (X4 ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2.2 in 13
  have eq27 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq28 (X0 X2 X3 X4 : G) : (((X3 ◇ X0) ◇ X0) ◇ X4) = (X4 ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.2 in 13
  have eq33 (X1 X2 X3 X4 : G) : (X2 ◇ X4) = (X4 ◇ ((X2 ◇ (X1 ◇ (X1 ◇ X3))) ◇ X2)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2.2.1 in 9
  have eq37 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ X4))) = ((X2 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq9 eq15 -- forward demodulation 15,9
  have eq42 (X0 X3 X4 : G) : (((X3 ◇ X0) ◇ X0) ◇ X4) = (X0 ◇ X4) := superpose eq9 eq28 -- forward demodulation 28,9
  have eq43 (X0 X2 X4 : G) : (X4 ◇ (X0 ◇ (X2 ◇ X0))) = (X0 ◇ X4) := superpose eq42 eq24 -- backward demodulation 24,42
  have eq45 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ X3) = (X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X4))) := superpose eq42 eq37 -- backward demodulation 37,42
  have eq46 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ (X2 ◇ X0))) = (X2 ◇ X3) := superpose eq42 eq13 -- backward demodulation 13,42
  have eq49 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ X3) := superpose eq42 eq27 -- backward demodulation 27,42
  have eq50 (X0 X2 X3 X4 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ X3) = (X3 ◇ (X2 ◇ (X2 ◇ X4))) := superpose eq42 eq45 -- forward demodulation 45,42
  have eq53 (X1 X2 X3 : G) : (X1 ◇ X3) = ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) := superpose eq46 eq18 -- backward demodulation 18,46
  have eq55 (X0 X2 X3 : G) : (X2 ◇ X3) = ((X2 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq46 eq50 -- backward demodulation 50,46
  have eq58 (X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X1) ◇ X3) := superpose eq46 eq53 -- forward demodulation 53,46
  have eq66 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ X1) ◇ X3) := superpose eq43 eq49 -- forward demodulation 49,43
  have eq67 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq66 eq9 -- backward demodulation 9,66
  have eq83 (X1 X2 X3 X4 : G) : (X2 ◇ X4) = (X4 ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X2)) := superpose eq66 eq33 -- forward demodulation 33,66
  have eq84 (X1 X2 X4 : G) : (X2 ◇ X4) = (X4 ◇ (X1 ◇ X2)) := superpose eq55 eq83 -- forward demodulation 83,55
  have eq90 : (sK2 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ sK0) := superpose eq84 eq10 -- backward demodulation 10,84
  have eq92 : (sK2 ◇ sK0) ≠ (sK0 ◇ sK2) := superpose eq84 eq90 -- forward demodulation 90,84
  have eq100 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := superpose eq67 eq58 -- superposition 58,67, 67 into 58, unify on (0).2 in 67 and (0).2 in 58
  have eq103 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq67 eq100 -- forward demodulation 100,67
  have eq138 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq67 eq103 -- superposition 103,67, 67 into 103, unify on (0).2 in 67 and (0).2 in 103
  have eq211 : (sK0 ◇ sK2) ≠ (sK0 ◇ sK2) := superpose eq138 eq92 -- superposition 92,138, 138 into 92, unify on (0).2 in 138 and (0).1 in 92
  subsumption eq211 rfl


@[equational_result]
theorem Equation3565_implies_Equation4376 (G : Type*) [Magma G] (h : Equation3565 G) : Equation4376 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X0) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (X3 ◇ ((X2 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ X4))) = (((X2 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq18 (X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X4))) = ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq24 (X0 X2 X3 X4 : G) : (((X3 ◇ X0) ◇ X0) ◇ X4) = (X4 ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2.2 in 13
  have eq27 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq28 (X0 X2 X3 X4 : G) : (((X3 ◇ X0) ◇ X0) ◇ X4) = (X4 ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.2 in 13
  have eq33 (X1 X2 X3 X4 : G) : (X2 ◇ X4) = (X4 ◇ ((X2 ◇ (X1 ◇ (X1 ◇ X3))) ◇ X2)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2.2.1 in 9
  have eq37 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ X4))) = ((X2 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq9 eq15 -- forward demodulation 15,9
  have eq42 (X0 X3 X4 : G) : (((X3 ◇ X0) ◇ X0) ◇ X4) = (X0 ◇ X4) := superpose eq9 eq28 -- forward demodulation 28,9
  have eq43 (X0 X2 X4 : G) : (X4 ◇ (X0 ◇ (X2 ◇ X0))) = (X0 ◇ X4) := superpose eq42 eq24 -- backward demodulation 24,42
  have eq45 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ X3) = (X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X4))) := superpose eq42 eq37 -- backward demodulation 37,42
  have eq46 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ (X2 ◇ X0))) = (X2 ◇ X3) := superpose eq42 eq13 -- backward demodulation 13,42
  have eq49 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ X3) := superpose eq42 eq27 -- backward demodulation 27,42
  have eq50 (X0 X2 X3 X4 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ X3) = (X3 ◇ (X2 ◇ (X2 ◇ X4))) := superpose eq42 eq45 -- forward demodulation 45,42
  have eq53 (X1 X2 X3 : G) : (X1 ◇ X3) = ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) := superpose eq46 eq18 -- backward demodulation 18,46
  have eq55 (X0 X2 X3 : G) : (X2 ◇ X3) = ((X2 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq46 eq50 -- backward demodulation 50,46
  have eq58 (X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X1) ◇ X3) := superpose eq46 eq53 -- forward demodulation 53,46
  have eq66 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ X1) ◇ X3) := superpose eq43 eq49 -- forward demodulation 49,43
  have eq67 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq66 eq9 -- backward demodulation 9,66
  have eq83 (X1 X2 X3 X4 : G) : (X2 ◇ X4) = (X4 ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X2)) := superpose eq66 eq33 -- forward demodulation 33,66
  have eq84 (X1 X2 X4 : G) : (X2 ◇ X4) = (X4 ◇ (X1 ◇ X2)) := superpose eq55 eq83 -- forward demodulation 83,55
  have eq90 : (sK3 ◇ (sK2 ◇ sK1)) ≠ (sK2 ◇ sK0) := superpose eq84 eq10 -- backward demodulation 10,84
  have eq92 : (sK2 ◇ sK0) ≠ (sK1 ◇ sK3) := superpose eq84 eq90 -- forward demodulation 90,84
  have eq100 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := superpose eq67 eq58 -- superposition 58,67, 67 into 58, unify on (0).2 in 67 and (0).2 in 58
  have eq103 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq67 eq100 -- forward demodulation 100,67
  have eq105 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose eq67 eq66 -- superposition 66,67, 67 into 66, unify on (0).2 in 67 and (0).2.1 in 66
  have eq112 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose eq58 eq105 -- forward demodulation 105,58
  have eq138 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq67 eq103 -- superposition 103,67, 67 into 103, unify on (0).2 in 67 and (0).2 in 103
  have eq151 : (sK1 ◇ sK3) ≠ (sK0 ◇ sK2) := superpose eq138 eq92 -- backward demodulation 92,138
  have eq229 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq66 eq112 -- superposition 112,66, 66 into 112, unify on (0).2 in 66 and (0).2 in 112
  have eq323 (X0 X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ X0) := superpose eq138 eq229 -- superposition 229,138, 138 into 229, unify on (0).2 in 138 and (0).1 in 229
  have eq362 (X0 : G) : (sK0 ◇ sK2) ≠ (X0 ◇ sK3) := superpose eq229 eq151 -- superposition 151,229, 229 into 151, unify on (0).2 in 229 and (0).1 in 151
  have eq503 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq323 eq323 -- superposition 323,323, 323 into 323, unify on (0).2 in 323 and (0).1 in 323
  have eq578 (X0 X1 : G) : (X1 ◇ X0) ≠ (sK0 ◇ sK2) := superpose eq323 eq362 -- superposition 362,323, 323 into 362, unify on (0).2 in 323 and (0).2 in 362
  subsumption eq578 eq503


@[equational_result]
theorem Equation3565_implies_Equation3964 (G : Type*) [Magma G] (h : Equation3565 G) : Equation3964 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X0) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (X3 ◇ ((X2 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq18 (X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X4))) = ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq24 (X0 X2 X3 X4 : G) : (((X3 ◇ X0) ◇ X0) ◇ X4) = (X4 ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2.2 in 13
  have eq27 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq28 (X0 X2 X3 X4 : G) : (((X3 ◇ X0) ◇ X0) ◇ X4) = (X4 ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.2 in 13
  have eq42 (X0 X3 X4 : G) : (((X3 ◇ X0) ◇ X0) ◇ X4) = (X0 ◇ X4) := superpose eq9 eq28 -- forward demodulation 28,9
  have eq43 (X0 X2 X4 : G) : (X4 ◇ (X0 ◇ (X2 ◇ X0))) = (X0 ◇ X4) := superpose eq42 eq24 -- backward demodulation 24,42
  have eq46 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ (X2 ◇ X0))) = (X2 ◇ X3) := superpose eq42 eq13 -- backward demodulation 13,42
  have eq47 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ X3) := superpose eq42 eq27 -- backward demodulation 27,42
  have eq53 (X1 X2 X3 : G) : (X1 ◇ X3) = ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) := superpose eq46 eq18 -- backward demodulation 18,46
  have eq58 (X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X1) ◇ X3) := superpose eq46 eq53 -- forward demodulation 53,46
  have eq60 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ X1) ◇ X3) := superpose eq43 eq47 -- forward demodulation 47,43
  have eq61 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq60 eq9 -- backward demodulation 9,60
  have eq65 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq61 eq10 -- backward demodulation 10,61
  have eq99 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := superpose eq61 eq58 -- superposition 58,61, 61 into 58, unify on (0).2 in 61 and (0).2 in 58
  have eq100 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq58 eq65 -- superposition 65,58, 58 into 65, unify on (0).2 in 58 and (0).2 in 65
  have eq103 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq61 eq99 -- forward demodulation 99,61
  have eq166 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq61 eq103 -- superposition 103,61, 61 into 103, unify on (0).2 in 61 and (0).2 in 103
  have eq267 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq166 eq100 -- superposition 100,166, 166 into 100, unify on (0).2 in 166 and (0).2 in 100
  subsumption eq267 rfl


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


@[equational_result]
theorem Equation3565_implies_Equation4299 (G : Type*) [Magma G] (h : Equation3565 G) : Equation4299 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X0) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (X3 ◇ ((X2 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq18 (X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X4))) = ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq24 (X0 X2 X3 X4 : G) : (((X3 ◇ X0) ◇ X0) ◇ X4) = (X4 ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2.2 in 13
  have eq27 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq28 (X0 X2 X3 X4 : G) : (((X3 ◇ X0) ◇ X0) ◇ X4) = (X4 ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.2 in 13
  have eq42 (X0 X3 X4 : G) : (((X3 ◇ X0) ◇ X0) ◇ X4) = (X0 ◇ X4) := superpose eq9 eq28 -- forward demodulation 28,9
  have eq43 (X0 X2 X4 : G) : (X4 ◇ (X0 ◇ (X2 ◇ X0))) = (X0 ◇ X4) := superpose eq42 eq24 -- backward demodulation 24,42
  have eq46 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ (X2 ◇ X0))) = (X2 ◇ X3) := superpose eq42 eq13 -- backward demodulation 13,42
  have eq49 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ X3) := superpose eq42 eq27 -- backward demodulation 27,42
  have eq53 (X1 X2 X3 : G) : (X1 ◇ X3) = ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) := superpose eq46 eq18 -- backward demodulation 18,46
  have eq58 (X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X1) ◇ X3) := superpose eq46 eq53 -- forward demodulation 53,46
  have eq66 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ X1) ◇ X3) := superpose eq43 eq49 -- forward demodulation 49,43
  have eq67 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq66 eq9 -- backward demodulation 9,66
  have eq71 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ sK2) := superpose eq67 eq10 -- backward demodulation 10,67
  have eq99 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := superpose eq67 eq58 -- superposition 58,67, 67 into 58, unify on (0).2 in 67 and (0).2 in 58
  have eq102 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq67 eq99 -- forward demodulation 99,67
  have eq104 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose eq67 eq66 -- superposition 66,67, 67 into 66, unify on (0).2 in 67 and (0).2.1 in 66
  have eq107 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ X2)) := superpose eq67 eq66 -- superposition 66,67, 67 into 66, unify on (0).2 in 67 and (0).2 in 66
  have eq111 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose eq58 eq104 -- forward demodulation 104,58
  have eq112 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ X1) := superpose eq67 eq107 -- forward demodulation 107,67
  have eq113 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK2) := superpose eq112 eq71 -- backward demodulation 71,112
  have eq165 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq67 eq102 -- superposition 102,67, 67 into 102, unify on (0).2 in 67 and (0).2 in 102
  have eq286 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq66 eq111 -- superposition 111,66, 66 into 111, unify on (0).2 in 66 and (0).2 in 111
  have eq323 (X0 X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ X0) := superpose eq165 eq286 -- superposition 286,165, 165 into 286, unify on (0).2 in 165 and (0).1 in 286
  have eq362 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK2) := superpose eq286 eq113 -- superposition 113,286, 286 into 113, unify on (0).2 in 286 and (0).2 in 113
  have eq503 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq323 eq323 -- superposition 323,323, 323 into 323, unify on (0).2 in 323 and (0).1 in 323
  have eq583 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X1 ◇ X0) := superpose eq323 eq362 -- superposition 362,323, 323 into 362, unify on (0).2 in 323 and (0).2 in 362
  subsumption eq583 eq503


@[equational_result]
theorem Equation3750_implies_Equation3271 (G : Type*) [Magma G] (h : Equation3750 G) : Equation3271 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq30 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq120 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq30 -- superposition 30,11, 11 into 30, unify on (0).2 in 11 and (0).2 in 30
  have eq134 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq120 -- forward demodulation 120,9
  have eq136 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq134 eq16 -- backward demodulation 16,134
  have eq167 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq9 eq134 -- superposition 134,9, 9 into 134, unify on (0).2 in 9 and (0).2.1 in 134
  have eq172 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq134 eq134 -- superposition 134,134, 134 into 134, unify on (0).2 in 134 and (0).2.1 in 134
  have eq181 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq134 eq15 -- superposition 15,134, 134 into 15, unify on (0).2 in 134 and (0).2.1 in 15
  have eq185 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq167 -- forward demodulation 167,9
  have eq209 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq172 -- forward demodulation 172,9
  have eq215 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ X1)) := superpose eq185 eq181 -- forward demodulation 181,185
  have eq216 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq209 eq215 -- forward demodulation 215,209
  have eq217 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := superpose eq216 eq136 -- backward demodulation 136,216
  have eq218 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq217 eq12 -- backward demodulation 12,217
  have eq231 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq217 eq10 -- backward demodulation 10,217
  have eq232 (X0 X1 X3 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq218 -- forward demodulation 218,9
  have eq264 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (X2 ◇ X3) := superpose eq232 eq217 -- superposition 217,232, 232 into 217, unify on (0).2 in 232 and (0).2 in 217
  have eq271 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq217 eq231 -- superposition 231,217, 217 into 231, unify on (0).2 in 217 and (0).2 in 231
  subsumption eq271 eq264


@[equational_result]
theorem Equation3750_implies_Equation3358 (G : Type*) [Magma G] (h : Equation3750 G) : Equation3358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq30 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq120 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq30 -- superposition 30,11, 11 into 30, unify on (0).2 in 11 and (0).2 in 30
  have eq134 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq120 -- forward demodulation 120,9
  have eq136 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq134 eq16 -- backward demodulation 16,134
  have eq167 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq9 eq134 -- superposition 134,9, 9 into 134, unify on (0).2 in 9 and (0).2.1 in 134
  have eq172 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq134 eq134 -- superposition 134,134, 134 into 134, unify on (0).2 in 134 and (0).2.1 in 134
  have eq181 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq134 eq15 -- superposition 15,134, 134 into 15, unify on (0).2 in 134 and (0).2.1 in 15
  have eq185 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq167 -- forward demodulation 167,9
  have eq209 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq172 -- forward demodulation 172,9
  have eq215 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ X1)) := superpose eq185 eq181 -- forward demodulation 181,185
  have eq216 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq209 eq215 -- forward demodulation 215,209
  have eq217 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := superpose eq216 eq136 -- backward demodulation 136,216
  have eq218 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq217 eq12 -- backward demodulation 12,217
  have eq231 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq217 eq10 -- backward demodulation 10,217
  have eq232 (X0 X1 X3 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq218 -- forward demodulation 218,9
  have eq264 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (X2 ◇ X3) := superpose eq232 eq217 -- superposition 217,232, 232 into 217, unify on (0).2 in 232 and (0).2 in 217
  have eq271 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK0) := superpose eq217 eq231 -- superposition 231,217, 217 into 231, unify on (0).2 in 217 and (0).2 in 231
  subsumption eq271 eq264


@[equational_result]
theorem Equation3975_implies_Equation4371 (G : Type*) [Magma G] (h : Equation3975 G) : Equation4371 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X1)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK3 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X2) = ((X2 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq19 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq32 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq33 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ X2) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.1 in 12
  have eq35 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) = ((((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X4) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.1.2 in 11
  have eq42 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq32 -- forward demodulation 32,9
  have eq45 (X0 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq42 eq19 -- backward demodulation 19,42
  have eq55 (X0 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X0) ◇ X2) := superpose eq42 eq33 -- forward demodulation 33,42
  have eq58 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) = ((((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ (X3 ◇ X1)) ◇ X4) := superpose eq42 eq35 -- forward demodulation 35,42
  have eq59 (X0 X1 X3 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ (X3 ◇ X1)) ◇ X4) := superpose eq42 eq58 -- forward demodulation 58,42
  have eq60 (X0 X1 X3 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X1)) = (((X3 ◇ X1) ◇ X1) ◇ X4) := superpose eq45 eq59 -- forward demodulation 59,45
  have eq61 (X0 X1 X4 : G) : (X4 ◇ X1) = (X4 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq45 eq60 -- forward demodulation 60,45
  have eq101 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq42 eq42 -- superposition 42,42, 42 into 42, unify on (0).2 in 42 and (0).2.2 in 42
  have eq102 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X2 ◇ (X3 ◇ X2)) ◇ X0) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).2 in 42
  have eq121 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq61 eq101 -- forward demodulation 101,61
  have eq125 (X0 X2 X3 : G) : (X3 ◇ X2) = ((X2 ◇ X0) ◇ X3) := superpose eq121 eq11 -- backward demodulation 11,121
  have eq126 : (sK2 ◇ (sK3 ◇ sK0)) ≠ (sK0 ◇ sK2) := superpose eq121 eq10 -- backward demodulation 10,121
  have eq129 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ X2) := superpose eq125 eq102 -- forward demodulation 102,125
  have eq130 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ X2) := superpose eq121 eq129 -- forward demodulation 129,121
  have eq188 : (sK0 ◇ sK2) ≠ (sK2 ◇ sK0) := superpose eq121 eq126 -- superposition 126,121, 121 into 126, unify on (0).2 in 121 and (0).1 in 126
  have eq202 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq55 eq130 -- superposition 130,55, 55 into 130, unify on (0).2 in 55 and (0).1 in 130
  have eq314 : (sK0 ◇ sK2) ≠ (sK0 ◇ sK2) := superpose eq202 eq188 -- superposition 188,202, 202 into 188, unify on (0).2 in 202 and (0).2 in 188
  subsumption eq314 rfl


@[equational_result]
theorem Equation3975_implies_Equation3601 (G : Type*) [Magma G] (h : Equation3975 G) : Equation3601 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X1)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK1 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X2) = ((X2 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X3) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1.2 in 11
  have eq19 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq20 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X1))) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq11 eq14 -- forward demodulation 14,11
  have eq32 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq33 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ X2) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.1 in 12
  have eq35 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) = ((((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X4) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.1.2 in 11
  have eq42 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq32 -- forward demodulation 32,9
  have eq45 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X0) ◇ X3) = (X3 ◇ X0) := superpose eq42 eq19 -- backward demodulation 19,42
  have eq49 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X1))) = (X3 ◇ X0) := superpose eq45 eq20 -- backward demodulation 20,45
  have eq55 (X0 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X0) ◇ X2) := superpose eq42 eq33 -- forward demodulation 33,42
  have eq58 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) = ((((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ (X3 ◇ X1)) ◇ X4) := superpose eq42 eq35 -- forward demodulation 35,42
  have eq59 (X0 X1 X3 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ (X3 ◇ X1)) ◇ X4) := superpose eq42 eq58 -- forward demodulation 58,42
  have eq60 (X0 X1 X3 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X1)) = (((X3 ◇ X1) ◇ X1) ◇ X4) := superpose eq45 eq59 -- forward demodulation 59,45
  have eq61 (X0 X1 X4 : G) : (X4 ◇ X1) = (X4 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq45 eq60 -- forward demodulation 60,45
  have eq101 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq42 eq42 -- superposition 42,42, 42 into 42, unify on (0).2 in 42 and (0).2.2 in 42
  have eq102 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X2 ◇ (X3 ◇ X2)) ◇ X0) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).2 in 42
  have eq121 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq61 eq101 -- forward demodulation 101,61
  have eq124 (X0 X1 X3 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ X1)) := superpose eq121 eq49 -- backward demodulation 49,121
  have eq125 (X0 X2 X3 : G) : (X3 ◇ X2) = ((X2 ◇ X0) ◇ X3) := superpose eq121 eq11 -- backward demodulation 11,121
  have eq128 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ sK1)) := superpose eq125 eq10 -- backward demodulation 10,125
  have eq129 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ X2) := superpose eq125 eq102 -- forward demodulation 102,125
  have eq130 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ X2) := superpose eq121 eq129 -- forward demodulation 129,121
  have eq180 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq124 eq121 -- superposition 121,124, 124 into 121, unify on (0).2 in 124 and (0).2 in 121
  have eq188 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK1) := superpose eq121 eq128 -- superposition 128,121, 121 into 128, unify on (0).2 in 121 and (0).2 in 128
  have eq202 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq55 eq130 -- superposition 130,55, 55 into 130, unify on (0).2 in 55 and (0).1 in 130
  have eq281 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq180 eq202 -- superposition 202,180, 180 into 202, unify on (0).2 in 180 and (0).1 in 202
  have eq302 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK2) := superpose eq202 eq188 -- superposition 188,202, 202 into 188, unify on (0).2 in 202 and (0).2 in 188
  subsumption eq302 eq281


@[equational_result]
theorem Equation3975_implies_Equation4209 (G : Type*) [Magma G] (h : Equation3975 G) : Equation4209 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X1)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X2) = ((X2 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X3) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1.2 in 11
  have eq19 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq20 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X1))) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq11 eq14 -- forward demodulation 14,11
  have eq32 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq35 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) = ((((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X4) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.1.2 in 11
  have eq42 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq32 -- forward demodulation 32,9
  have eq45 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X0) ◇ X3) = (X3 ◇ X0) := superpose eq42 eq19 -- backward demodulation 19,42
  have eq49 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X1))) = (X3 ◇ X0) := superpose eq45 eq20 -- backward demodulation 20,45
  have eq58 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) = ((((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ (X3 ◇ X1)) ◇ X4) := superpose eq42 eq35 -- forward demodulation 35,42
  have eq59 (X0 X1 X3 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ (X3 ◇ X1)) ◇ X4) := superpose eq42 eq58 -- forward demodulation 58,42
  have eq60 (X0 X1 X3 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X1)) = (((X3 ◇ X1) ◇ X1) ◇ X4) := superpose eq45 eq59 -- forward demodulation 59,45
  have eq61 (X0 X1 X4 : G) : (X4 ◇ X1) = (X4 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq45 eq60 -- forward demodulation 60,45
  have eq101 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq42 eq42 -- superposition 42,42, 42 into 42, unify on (0).2 in 42 and (0).2.2 in 42
  have eq103 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = ((X2 ◇ (X3 ◇ X2)) ◇ X0) := superpose eq11 eq42 -- superposition 42,11, 11 into 42, unify on (0).2 in 11 and (0).2 in 42
  have eq121 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq61 eq101 -- forward demodulation 101,61
  have eq124 (X0 X1 X3 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ X1)) := superpose eq121 eq49 -- backward demodulation 49,121
  have eq125 (X0 X2 X3 : G) : (X3 ◇ X2) = ((X2 ◇ X0) ◇ X3) := superpose eq121 eq11 -- backward demodulation 11,121
  have eq128 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK1) := superpose eq125 eq10 -- backward demodulation 10,125
  have eq131 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ X2) := superpose eq125 eq103 -- forward demodulation 103,125
  have eq132 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq121 eq131 -- forward demodulation 131,121
  have eq180 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq124 eq121 -- superposition 121,124, 124 into 121, unify on (0).2 in 124 and (0).2 in 121
  have eq220 (X0 : G) : (sK0 ◇ sK1) ≠ ((sK0 ◇ X0) ◇ sK1) := superpose eq180 eq128 -- superposition 128,180, 180 into 128, unify on (0).2 in 180 and (0).2.1 in 128
  subsumption eq220 eq132


@[equational_result]
theorem Equation3975_implies_Equation3751 (G : Type*) [Magma G] (h : Equation3975 G) : Equation3751 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X1)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X2) = ((X2 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq19 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq32 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq35 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) = ((((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X4) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.1.2 in 11
  have eq42 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq32 -- forward demodulation 32,9
  have eq45 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X0) ◇ X3) = (X3 ◇ X0) := superpose eq42 eq19 -- backward demodulation 19,42
  have eq58 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) = ((((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ (X3 ◇ X1)) ◇ X4) := superpose eq42 eq35 -- forward demodulation 35,42
  have eq59 (X0 X1 X3 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ (X3 ◇ X1)) ◇ X4) := superpose eq42 eq58 -- forward demodulation 58,42
  have eq60 (X0 X1 X3 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X1)) = (((X3 ◇ X1) ◇ X1) ◇ X4) := superpose eq45 eq59 -- forward demodulation 59,45
  have eq61 (X0 X1 X4 : G) : (X4 ◇ X1) = (X4 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq45 eq60 -- forward demodulation 60,45
  have eq101 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq42 eq42 -- superposition 42,42, 42 into 42, unify on (0).2 in 42 and (0).2.2 in 42
  have eq121 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq61 eq101 -- forward demodulation 101,61
  have eq125 (X0 X2 X3 : G) : (X3 ◇ X2) = ((X2 ◇ X0) ◇ X3) := superpose eq121 eq11 -- backward demodulation 11,121
  have eq182 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq121 eq10 -- superposition 10,121, 121 into 10, unify on (0).2 in 121 and (0).2 in 10
  subsumption eq182 eq125


@[equational_result]
theorem Equation3975_implies_Equation3302 (G : Type*) [Magma G] (h : Equation3975 G) : Equation3302 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X1)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X2) = ((X2 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X3) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1.2 in 11
  have eq19 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq20 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X1))) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq11 eq14 -- forward demodulation 14,11
  have eq32 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq33 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ X2) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.1 in 12
  have eq35 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) = ((((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X4) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.1.2 in 11
  have eq42 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq32 -- forward demodulation 32,9
  have eq45 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X0) ◇ X3) = (X3 ◇ X0) := superpose eq42 eq19 -- backward demodulation 19,42
  have eq49 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X1))) = (X3 ◇ X0) := superpose eq45 eq20 -- backward demodulation 20,45
  have eq55 (X0 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X0) ◇ X2) := superpose eq42 eq33 -- forward demodulation 33,42
  have eq58 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) = ((((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ (X3 ◇ X1)) ◇ X4) := superpose eq42 eq35 -- forward demodulation 35,42
  have eq59 (X0 X1 X3 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ (X3 ◇ X1)) ◇ X4) := superpose eq42 eq58 -- forward demodulation 58,42
  have eq60 (X0 X1 X3 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X1)) = (((X3 ◇ X1) ◇ X1) ◇ X4) := superpose eq45 eq59 -- forward demodulation 59,45
  have eq61 (X0 X1 X4 : G) : (X4 ◇ X1) = (X4 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq45 eq60 -- forward demodulation 60,45
  have eq101 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq42 eq42 -- superposition 42,42, 42 into 42, unify on (0).2 in 42 and (0).2.2 in 42
  have eq102 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X2 ◇ (X3 ◇ X2)) ◇ X0) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).2 in 42
  have eq113 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK2) := superpose eq42 eq10 -- superposition 10,42, 42 into 10, unify on (0).2 in 42 and (0).2 in 10
  have eq122 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq61 eq101 -- forward demodulation 101,61
  have eq125 (X0 X1 X3 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ X1)) := superpose eq122 eq49 -- backward demodulation 49,122
  have eq126 (X0 X2 X3 : G) : (X3 ◇ X2) = ((X2 ◇ X0) ◇ X3) := superpose eq122 eq11 -- backward demodulation 11,122
  have eq130 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ X2) := superpose eq126 eq102 -- forward demodulation 102,126
  have eq131 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ X2) := superpose eq122 eq130 -- forward demodulation 130,122
  have eq182 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq125 eq122 -- superposition 122,125, 125 into 122, unify on (0).2 in 125 and (0).2 in 122
  have eq222 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ X0) := superpose eq182 eq113 -- superposition 113,182, 182 into 113, unify on (0).2 in 182 and (0).2 in 113
  have eq246 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq55 eq131 -- superposition 131,55, 55 into 131, unify on (0).2 in 55 and (0).1 in 131
  have eq275 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq182 eq246 -- superposition 246,182, 182 into 246, unify on (0).2 in 182 and (0).1 in 246
  have eq405 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq275 eq275 -- superposition 275,275, 275 into 275, unify on (0).2 in 275 and (0).1 in 275
  have eq445 (X0 X1 : G) : (X0 ◇ X1) ≠ (sK0 ◇ sK0) := superpose eq275 eq222 -- superposition 222,275, 275 into 222, unify on (0).2 in 275 and (0).2 in 222
  subsumption eq445 eq405


@[equational_result]
theorem Equation3975_implies_Equation4001 (G : Type*) [Magma G] (h : Equation3975 G) : Equation4001 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X1)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK0 ◇ sK3)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X2) = ((X2 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X3) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1.2 in 11
  have eq19 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq20 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X1))) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq11 eq14 -- forward demodulation 14,11
  have eq32 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq33 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ X2) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.1 in 12
  have eq35 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) = ((((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X4) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.1.2 in 11
  have eq42 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq32 -- forward demodulation 32,9
  have eq45 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X0) ◇ X3) = (X3 ◇ X0) := superpose eq42 eq19 -- backward demodulation 19,42
  have eq49 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X1))) = (X3 ◇ X0) := superpose eq45 eq20 -- backward demodulation 20,45
  have eq55 (X0 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X0) ◇ X2) := superpose eq42 eq33 -- forward demodulation 33,42
  have eq58 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) = ((((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ (X3 ◇ X1)) ◇ X4) := superpose eq42 eq35 -- forward demodulation 35,42
  have eq59 (X0 X1 X3 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ (X3 ◇ X1)) ◇ X4) := superpose eq42 eq58 -- forward demodulation 58,42
  have eq60 (X0 X1 X3 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X1)) = (((X3 ◇ X1) ◇ X1) ◇ X4) := superpose eq45 eq59 -- forward demodulation 59,45
  have eq61 (X0 X1 X4 : G) : (X4 ◇ X1) = (X4 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq45 eq60 -- forward demodulation 60,45
  have eq101 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq42 eq42 -- superposition 42,42, 42 into 42, unify on (0).2 in 42 and (0).2.2 in 42
  have eq102 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X2 ◇ (X3 ◇ X2)) ◇ X0) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).2 in 42
  have eq121 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq61 eq101 -- forward demodulation 101,61
  have eq124 (X0 X1 X3 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ X1)) := superpose eq121 eq49 -- backward demodulation 49,121
  have eq125 (X0 X2 X3 : G) : (X3 ◇ X2) = ((X2 ◇ X0) ◇ X3) := superpose eq121 eq11 -- backward demodulation 11,121
  have eq126 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK3) ◇ sK1) := superpose eq121 eq10 -- backward demodulation 10,121
  have eq129 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ X2) := superpose eq125 eq102 -- forward demodulation 102,125
  have eq130 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ X2) := superpose eq121 eq129 -- forward demodulation 129,121
  have eq139 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK2) := superpose eq125 eq126 -- superposition 126,125, 125 into 126, unify on (0).2 in 125 and (0).2 in 126
  have eq180 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq124 eq121 -- superposition 121,124, 124 into 121, unify on (0).2 in 124 and (0).2 in 121
  have eq220 (X0 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ X0) := superpose eq180 eq139 -- superposition 139,180, 180 into 139, unify on (0).2 in 180 and (0).2 in 139
  have eq243 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq55 eq130 -- superposition 130,55, 55 into 130, unify on (0).2 in 55 and (0).1 in 130
  have eq272 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq180 eq243 -- superposition 243,180, 180 into 243, unify on (0).2 in 180 and (0).1 in 243
  have eq468 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq272 eq272 -- superposition 272,272, 272 into 272, unify on (0).2 in 272 and (0).1 in 272
  have eq512 (X0 X1 : G) : (X0 ◇ X1) ≠ (sK0 ◇ sK1) := superpose eq272 eq220 -- superposition 220,272, 272 into 220, unify on (0).2 in 272 and (0).2 in 220
  subsumption eq512 eq468


@[equational_result]
theorem Equation3975_implies_Equation3349 (G : Type*) [Magma G] (h : Equation3975 G) : Equation3349 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X1)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X2) = ((X2 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X3) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1.2 in 11
  have eq19 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq20 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X1))) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq11 eq14 -- forward demodulation 14,11
  have eq32 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq33 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ X2) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.1 in 12
  have eq35 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) = ((((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X4) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.1.2 in 11
  have eq42 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq32 -- forward demodulation 32,9
  have eq45 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X0) ◇ X3) = (X3 ◇ X0) := superpose eq42 eq19 -- backward demodulation 19,42
  have eq49 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X1))) = (X3 ◇ X0) := superpose eq45 eq20 -- backward demodulation 20,45
  have eq55 (X0 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X0) ◇ X2) := superpose eq42 eq33 -- forward demodulation 33,42
  have eq58 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) = ((((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ (X3 ◇ X1)) ◇ X4) := superpose eq42 eq35 -- forward demodulation 35,42
  have eq59 (X0 X1 X3 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ (X3 ◇ X1)) ◇ X4) := superpose eq42 eq58 -- forward demodulation 58,42
  have eq60 (X0 X1 X3 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X1)) = (((X3 ◇ X1) ◇ X1) ◇ X4) := superpose eq45 eq59 -- forward demodulation 59,45
  have eq61 (X0 X1 X4 : G) : (X4 ◇ X1) = (X4 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq45 eq60 -- forward demodulation 60,45
  have eq101 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq42 eq42 -- superposition 42,42, 42 into 42, unify on (0).2 in 42 and (0).2.2 in 42
  have eq102 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X2 ◇ (X3 ◇ X2)) ◇ X0) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).2 in 42
  have eq121 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq61 eq101 -- forward demodulation 101,61
  have eq124 (X0 X1 X3 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ X1)) := superpose eq121 eq49 -- backward demodulation 49,121
  have eq125 (X0 X2 X3 : G) : (X3 ◇ X2) = ((X2 ◇ X0) ◇ X3) := superpose eq121 eq11 -- backward demodulation 11,121
  have eq126 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq121 eq10 -- backward demodulation 10,121
  have eq129 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ X2) := superpose eq125 eq102 -- forward demodulation 102,125
  have eq130 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ X2) := superpose eq121 eq129 -- forward demodulation 129,121
  have eq151 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq124 eq126 -- superposition 126,124, 124 into 126, unify on (0).2 in 124 and (0).2 in 126
  have eq202 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq55 eq130 -- superposition 130,55, 55 into 130, unify on (0).2 in 55 and (0).1 in 130
  have eq354 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq202 eq151 -- superposition 151,202, 202 into 151, unify on (0).2 in 202 and (0).2 in 151
  subsumption eq354 rfl


@[equational_result]
theorem Equation3975_implies_Equation3971 (G : Type*) [Magma G] (h : Equation3975 G) : Equation3971 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X1)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X2) = ((X2 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq19 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq32 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq35 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) = ((((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X4) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.1.2 in 11
  have eq42 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq32 -- forward demodulation 32,9
  have eq45 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X0) ◇ X3) = (X3 ◇ X0) := superpose eq42 eq19 -- backward demodulation 19,42
  have eq58 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) = ((((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ (X3 ◇ X1)) ◇ X4) := superpose eq42 eq35 -- forward demodulation 35,42
  have eq59 (X0 X1 X3 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ (X3 ◇ X1)) ◇ X4) := superpose eq42 eq58 -- forward demodulation 58,42
  have eq60 (X0 X1 X3 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X1)) = (((X3 ◇ X1) ◇ X1) ◇ X4) := superpose eq45 eq59 -- forward demodulation 59,45
  have eq61 (X0 X1 X4 : G) : (X4 ◇ X1) = (X4 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq45 eq60 -- forward demodulation 60,45
  have eq101 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq42 eq42 -- superposition 42,42, 42 into 42, unify on (0).2 in 42 and (0).2.2 in 42
  have eq121 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq61 eq101 -- forward demodulation 101,61
  have eq125 (X0 X2 X3 : G) : (X3 ◇ X2) = ((X2 ◇ X0) ◇ X3) := superpose eq121 eq11 -- backward demodulation 11,121
  have eq126 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq121 eq10 -- backward demodulation 10,121
  subsumption eq126 eq125


@[equational_result]
theorem Equation4212_implies_Equation3889 (G : Type*) [Magma G] (h : Equation4212 G) : Equation3889 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X1) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X3 ◇ X2) = (((X2 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq22 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq23 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1 in 11
  have eq32 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq34 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK2) := superpose eq32 eq10 -- backward demodulation 10,32
  have eq36 (X0 X1 X2 : G) : (X2 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq32 eq23 -- forward demodulation 23,32
  have eq75 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X3) := superpose eq9 eq32 -- superposition 32,9, 9 into 32, unify on (0).2 in 9 and (0).2 in 32
  have eq89 (X1 X2 X3 : G) : (X3 ◇ X1) = ((X2 ◇ X3) ◇ X1) := superpose eq9 eq75 -- forward demodulation 75,9
  have eq94 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X0) ◇ X2) := superpose eq89 eq36 -- backward demodulation 36,89
  have eq95 (X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ X2) ◇ X3) := superpose eq89 eq11 -- backward demodulation 11,89
  have eq126 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ X0) := superpose eq95 eq94 -- superposition 94,95, 95 into 94, unify on (0).2 in 95 and (0).2 in 94
  have eq146 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq95 eq126 -- superposition 126,95, 95 into 126, unify on (0).2 in 95 and (0).1 in 126
  have eq168 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ X0) := superpose eq126 eq34 -- superposition 34,126, 126 into 34, unify on (0).2 in 126 and (0).2 in 34
  subsumption eq168 eq146


@[equational_result]
theorem Equation4212_implies_Equation3254 (G : Type*) [Magma G] (h : Equation4212 G) : Equation3254 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X1) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X3 ◇ X2) = (((X2 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq22 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq23 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1 in 11
  have eq32 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq34 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq32 eq10 -- backward demodulation 10,32
  have eq36 (X0 X1 X2 : G) : (X2 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq32 eq23 -- forward demodulation 23,32
  have eq75 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X3) := superpose eq9 eq32 -- superposition 32,9, 9 into 32, unify on (0).2 in 9 and (0).2 in 32
  have eq87 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK1) := superpose eq32 eq34 -- superposition 34,32, 32 into 34, unify on (0).2 in 32 and (0).2 in 34
  have eq90 (X1 X2 X3 : G) : (X3 ◇ X1) = ((X2 ◇ X3) ◇ X1) := superpose eq9 eq75 -- forward demodulation 75,9
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X0) ◇ X2) := superpose eq90 eq36 -- backward demodulation 36,90
  have eq96 (X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ X2) ◇ X3) := superpose eq90 eq11 -- backward demodulation 11,90
  have eq126 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ X0) := superpose eq96 eq95 -- superposition 95,96, 96 into 95, unify on (0).2 in 96 and (0).2 in 95
  have eq167 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq126 eq87 -- superposition 87,126, 126 into 87, unify on (0).2 in 126 and (0).2 in 87
  subsumption eq167 eq126


@[equational_result]
theorem Equation4212_implies_Equation4175 (G : Type*) [Magma G] (h : Equation4212 G) : Equation4175 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X1) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X3 ◇ X2) = (((X2 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq22 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq32 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq74 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X3) := superpose eq9 eq32 -- superposition 32,9, 9 into 32, unify on (0).2 in 9 and (0).2 in 32
  have eq88 (X1 X2 X3 : G) : (X3 ◇ X1) = ((X2 ◇ X3) ◇ X1) := superpose eq9 eq74 -- forward demodulation 74,9
  have eq95 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK0) ◇ sK1) := superpose eq88 eq10 -- backward demodulation 10,88
  subsumption eq95 eq88


@[equational_result]
theorem Equation4212_implies_Equation3558 (G : Type*) [Magma G] (h : Equation4212 G) : Equation3558 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X1) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X3 ◇ X2) = (((X2 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq9 eq15 -- forward demodulation 15,9
  have eq24 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).2 in 19
  have eq34 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = (X1 ◇ X0) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq46 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq47 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1 in 11
  have eq60 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq63 (X0 X1 X2 : G) : (X2 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq60 eq47 -- forward demodulation 47,60
  have eq75 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X3) := superpose eq9 eq60 -- superposition 60,9, 9 into 60, unify on (0).2 in 9 and (0).2 in 60
  have eq90 (X1 X2 X3 : G) : (X3 ◇ X1) = ((X2 ◇ X3) ◇ X1) := superpose eq9 eq75 -- forward demodulation 75,9
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X0) ◇ X2) := superpose eq90 eq63 -- backward demodulation 63,90
  have eq96 (X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ X2) ◇ X3) := superpose eq90 eq11 -- backward demodulation 11,90
  have eq126 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ X0) := superpose eq96 eq95 -- superposition 95,96, 96 into 95, unify on (0).2 in 96 and (0).2 in 95
  have eq168 (X0 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ X0) := superpose eq126 eq13 -- superposition 13,126, 126 into 13, unify on (0).2 in 126 and (0).2 in 13
  have eq191 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq12 eq34 -- superposition 34,12, 12 into 34, unify on (0).2 in 12 and (0).1 in 34
  have eq281 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq191 eq168 -- superposition 168,191, 191 into 168, unify on (0).2 in 191 and (0).2 in 168
  subsumption eq281 rfl


@[equational_result]
theorem Equation4212_implies_Equation3917 (G : Type*) [Magma G] (h : Equation4212 G) : Equation3917 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X1) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X3 ◇ X2) = (((X2 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq22 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq23 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1 in 11
  have eq32 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq34 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq32 eq10 -- backward demodulation 10,32
  have eq36 (X0 X1 X2 : G) : (X2 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq32 eq23 -- forward demodulation 23,32
  have eq75 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X3) := superpose eq9 eq32 -- superposition 32,9, 9 into 32, unify on (0).2 in 9 and (0).2 in 32
  have eq89 (X1 X2 X3 : G) : (X3 ◇ X1) = ((X2 ◇ X3) ◇ X1) := superpose eq9 eq75 -- forward demodulation 75,9
  have eq94 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X0) ◇ X2) := superpose eq89 eq36 -- backward demodulation 36,89
  have eq95 (X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ X2) ◇ X3) := superpose eq89 eq11 -- backward demodulation 11,89
  have eq96 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq94 eq34 -- backward demodulation 34,94
  have eq126 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ X0) := superpose eq95 eq94 -- superposition 94,95, 95 into 94, unify on (0).2 in 95 and (0).2 in 94
  have eq167 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq126 eq96 -- superposition 96,126, 126 into 96, unify on (0).2 in 126 and (0).1 in 96
  subsumption eq167 eq126


@[equational_result]
theorem Equation4212_implies_Equation3750 (G : Type*) [Magma G] (h : Equation4212 G) : Equation3750 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X1) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X3 ◇ X2) = (((X2 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq22 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq23 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1 in 11
  have eq32 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq35 (X0 X1 X2 : G) : (X2 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq32 eq23 -- forward demodulation 23,32
  have eq74 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X3) := superpose eq9 eq32 -- superposition 32,9, 9 into 32, unify on (0).2 in 9 and (0).2 in 32
  have eq89 (X1 X2 X3 : G) : (X3 ◇ X1) = ((X2 ◇ X3) ◇ X1) := superpose eq9 eq74 -- forward demodulation 74,9
  have eq94 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X0) ◇ X2) := superpose eq89 eq35 -- backward demodulation 35,89
  have eq95 (X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ X2) ◇ X3) := superpose eq89 eq11 -- backward demodulation 11,89
  have eq127 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ X0) := superpose eq95 eq94 -- superposition 94,95, 95 into 94, unify on (0).2 in 95 and (0).2 in 94
  have eq146 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ X3) := superpose eq94 eq127 -- superposition 127,94, 94 into 127, unify on (0).2 in 94 and (0).1 in 127
  have eq169 (X0 : G) : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ X0) := superpose eq127 eq10 -- superposition 10,127, 127 into 10, unify on (0).2 in 127 and (0).2 in 10
  subsumption eq169 eq146


@[equational_result]
theorem Equation3551_implies_Equation3926 (G : Type*) [Magma G] (h : Equation3551 G) : Equation3926 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK2) := mod_symm nh
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
  have eq128 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq125 eq10 -- backward demodulation 10,125
  have eq129 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq125 eq102 -- forward demodulation 102,125
  have eq130 (X0 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X0)) := superpose eq121 eq129 -- forward demodulation 129,121
  have eq185 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X2) := superpose eq124 eq121 -- superposition 121,124, 124 into 121, unify on (0).2 in 124 and (0).2 in 121
  have eq201 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ (X1 ◇ X1)) := superpose eq55 eq185 -- superposition 185,55, 55 into 185, unify on (0).2 in 55 and (0).1 in 185
  have eq249 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq55 eq130 -- superposition 130,55, 55 into 130, unify on (0).2 in 55 and (0).2 in 130
  have eq296 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK0)) := superpose eq249 eq128 -- superposition 128,249, 249 into 128, unify on (0).2 in 249 and (0).2 in 128
  subsumption eq296 eq201


@[equational_result]
theorem Equation3551_implies_Equation3317 (G : Type*) [Magma G] (h : Equation3551 G) : Equation3317 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
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
  have eq121 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq61 eq101 -- forward demodulation 101,61
  have eq124 (X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ X2) ◇ X3) := superpose eq121 eq49 -- backward demodulation 49,121
  have eq125 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq121 eq11 -- backward demodulation 11,121
  have eq128 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK1)) := superpose eq125 eq10 -- backward demodulation 10,125
  have eq150 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ X2)) := superpose eq55 eq124 -- superposition 124,55, 55 into 124, unify on (0).2 in 55 and (0).2 in 124
  have eq158 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq55 eq150 -- forward demodulation 150,55
  have eq184 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X2) := superpose eq124 eq121 -- superposition 121,124, 124 into 121, unify on (0).2 in 124 and (0).2 in 121
  have eq225 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq184 eq128 -- superposition 128,184, 184 into 128, unify on (0).2 in 184 and (0).2.2 in 128
  subsumption eq225 eq158


@[equational_result]
theorem Equation3551_implies_Equation4620 (G : Type*) [Magma G] (h : Equation3551 G) : Equation4620 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ X3) = (X3 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.1 in 11
  have eq19 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.2 in 12
  have eq36 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) ◇ X4) = (X4 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3))))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq42 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq9 eq32 -- forward demodulation 32,9
  have eq45 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ X3) := superpose eq42 eq19 -- backward demodulation 19,42
  have eq55 (X0 X2 : G) : (X0 ◇ X2) = (X2 ◇ (X0 ◇ X0)) := superpose eq42 eq33 -- forward demodulation 33,42
  have eq60 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) ◇ X4) = (X4 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3))))) := superpose eq42 eq36 -- forward demodulation 36,42
  have eq61 (X0 X1 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X4 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X3))))) := superpose eq42 eq60 -- forward demodulation 60,42
  have eq62 (X0 X1 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X4 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq45 eq61 -- forward demodulation 61,45
  have eq63 (X1 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X1 ◇ X4) := superpose eq45 eq62 -- forward demodulation 62,45
  have eq76 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq55 eq55 -- superposition 55,55, 55 into 55, unify on (0).2 in 55 and (0).2.2 in 55
  have eq85 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose eq45 eq76 -- forward demodulation 76,45
  have eq86 : ((sK2 ◇ sK1) ◇ sK2) ≠ (sK0 ◇ sK1) := superpose eq85 eq10 -- backward demodulation 10,85
  have eq98 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := superpose eq11 eq85 -- superposition 85,11, 11 into 85, unify on (0).2 in 11 and (0).2 in 85
  have eq115 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq55 eq98 -- forward demodulation 98,55
  have eq132 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq42 eq42 -- superposition 42,42, 42 into 42, unify on (0).2 in 42 and (0).2.1 in 42
  have eq155 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq63 eq132 -- forward demodulation 132,63
  have eq159 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := superpose eq155 eq115 -- backward demodulation 115,155
  have eq161 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq155 eq11 -- backward demodulation 11,155
  have eq163 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq159 eq45 -- backward demodulation 45,159
  have eq204 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq161 eq163 -- superposition 163,161, 161 into 163, unify on (0).2 in 161 and (0).2 in 163
  have eq221 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ (X1 ◇ X1)) := superpose eq55 eq204 -- superposition 204,55, 55 into 204, unify on (0).2 in 55 and (0).1 in 204
  have eq245 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK2) := superpose eq204 eq86 -- superposition 86,204, 204 into 86, unify on (0).2 in 204 and (0).1 in 86
  have eq287 (X0 X1 : G) : (X0 ◇ sK1) ≠ (X1 ◇ sK2) := superpose eq204 eq245 -- superposition 245,204, 204 into 245, unify on (0).2 in 204 and (0).1 in 245
  have eq349 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X0) := superpose eq163 eq159 -- superposition 159,163, 163 into 159, unify on (0).2 in 163 and (0).2 in 159
  have eq509 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq221 eq349 -- superposition 349,221, 221 into 349, unify on (0).2 in 221 and (0).1 in 349
  have eq561 (X0 X1 X2 : G) : (X1 ◇ X0) ≠ (X2 ◇ sK2) := superpose eq349 eq287 -- superposition 287,349, 349 into 287, unify on (0).2 in 349 and (0).1 in 287
  subsumption eq561 eq509


@[equational_result]
theorem Equation3551_implies_Equation4678 (G : Type*) [Magma G] (h : Equation3551 G) : Equation4678 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK1 ◇ sK0) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ X3) = (X3 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.1 in 11
  have eq14 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (X3 ◇ ((X2 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.1 in 11
  have eq19 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq20 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq11 eq14 -- forward demodulation 14,11
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.2 in 12
  have eq36 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) ◇ X4) = (X4 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3))))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq42 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq9 eq32 -- forward demodulation 32,9
  have eq45 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ X3) := superpose eq42 eq19 -- backward demodulation 19,42
  have eq49 (X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (X2 ◇ X3) := superpose eq45 eq20 -- backward demodulation 20,45
  have eq55 (X0 X2 : G) : (X0 ◇ X2) = (X2 ◇ (X0 ◇ X0)) := superpose eq42 eq33 -- forward demodulation 33,42
  have eq60 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) ◇ X4) = (X4 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3))))) := superpose eq42 eq36 -- forward demodulation 36,42
  have eq61 (X0 X1 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X4 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X3))))) := superpose eq42 eq60 -- forward demodulation 60,42
  have eq62 (X0 X1 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X4 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq45 eq61 -- forward demodulation 61,45
  have eq63 (X1 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X1 ◇ X4) := superpose eq45 eq62 -- forward demodulation 62,45
  have eq99 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq42 eq42 -- superposition 42,42, 42 into 42, unify on (0).2 in 42 and (0).2.1 in 42
  have eq100 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ ((X2 ◇ X3) ◇ X2)) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).2 in 42
  have eq119 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq63 eq99 -- forward demodulation 99,63
  have eq122 (X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ X2) ◇ X3) := superpose eq119 eq49 -- backward demodulation 49,119
  have eq123 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq119 eq11 -- backward demodulation 11,119
  have eq124 : ((sK1 ◇ sK0) ◇ sK3) ≠ (sK0 ◇ sK2) := superpose eq119 eq10 -- backward demodulation 10,119
  have eq127 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq123 eq100 -- forward demodulation 100,123
  have eq128 (X0 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X0)) := superpose eq119 eq127 -- forward demodulation 127,119
  have eq149 : (sK0 ◇ sK2) ≠ (sK0 ◇ sK3) := superpose eq122 eq124 -- superposition 124,122, 122 into 124, unify on (0).2 in 122 and (0).1 in 124
  have eq182 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X2) := superpose eq122 eq119 -- superposition 119,122, 122 into 119, unify on (0).2 in 122 and (0).2 in 119
  have eq204 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq55 eq128 -- superposition 128,55, 55 into 128, unify on (0).2 in 55 and (0).2 in 128
  have eq255 (X0 : G) : (sK0 ◇ sK2) ≠ (X0 ◇ sK3) := superpose eq182 eq149 -- superposition 149,182, 182 into 149, unify on (0).2 in 182 and (0).2 in 149
  have eq283 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X1) := superpose eq182 eq204 -- superposition 204,182, 182 into 204, unify on (0).2 in 182 and (0).1 in 204
  have eq417 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq283 eq283 -- superposition 283,283, 283 into 283, unify on (0).2 in 283 and (0).1 in 283
  have eq454 (X0 X1 : G) : (X1 ◇ X0) ≠ (sK0 ◇ sK2) := superpose eq283 eq255 -- superposition 255,283, 283 into 255, unify on (0).2 in 283 and (0).2 in 255
  subsumption eq454 eq417


@[equational_result]
theorem Equation3551_implies_Equation4612 (G : Type*) [Magma G] (h : Equation3551 G) : Equation4612 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ X3) = (X3 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.1 in 11
  have eq19 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.2 in 12
  have eq36 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) ◇ X4) = (X4 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2.1 in 11
  have eq42 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq9 eq32 -- forward demodulation 32,9
  have eq45 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ X3) := superpose eq42 eq19 -- backward demodulation 19,42
  have eq55 (X0 X2 : G) : (X0 ◇ X2) = (X2 ◇ (X0 ◇ X0)) := superpose eq42 eq33 -- forward demodulation 33,42
  have eq60 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X4 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (X1 ◇ (X1 ◇ X3)))) := superpose eq42 eq36 -- forward demodulation 36,42
  have eq61 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X4 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0))) := superpose eq45 eq60 -- forward demodulation 60,45
  have eq62 (X0 X1 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X4 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq42 eq61 -- forward demodulation 61,42
  have eq63 (X1 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X1 ◇ X4) := superpose eq45 eq62 -- forward demodulation 62,45
  have eq76 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq55 eq55 -- superposition 55,55, 55 into 55, unify on (0).2 in 55 and (0).2.2 in 55
  have eq85 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose eq45 eq76 -- forward demodulation 76,45
  have eq86 : ((sK1 ◇ sK2) ◇ sK2) ≠ (sK0 ◇ sK1) := superpose eq85 eq10 -- backward demodulation 10,85
  have eq98 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := superpose eq11 eq85 -- superposition 85,11, 11 into 85, unify on (0).2 in 11 and (0).2 in 85
  have eq99 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := superpose eq55 eq85 -- superposition 85,55, 55 into 85, unify on (0).2 in 55 and (0).2 in 85
  have eq115 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq55 eq98 -- forward demodulation 98,55
  have eq116 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq55 eq99 -- forward demodulation 99,55
  have eq132 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq42 eq42 -- superposition 42,42, 42 into 42, unify on (0).2 in 42 and (0).2.1 in 42
  have eq155 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq63 eq132 -- forward demodulation 132,63
  have eq159 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := superpose eq155 eq115 -- backward demodulation 115,155
  have eq161 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq155 eq11 -- backward demodulation 11,155
  have eq163 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq159 eq45 -- backward demodulation 45,159
  have eq204 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq161 eq163 -- superposition 163,161, 161 into 163, unify on (0).2 in 161 and (0).2 in 163
  have eq246 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK2) := superpose eq204 eq86 -- superposition 86,204, 204 into 86, unify on (0).2 in 204 and (0).1 in 86
  have eq287 (X0 X1 : G) : (X0 ◇ sK1) ≠ (X1 ◇ sK2) := superpose eq204 eq246 -- superposition 246,204, 204 into 246, unify on (0).2 in 204 and (0).1 in 246
  have eq323 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq55 eq116 -- superposition 116,55, 55 into 116, unify on (0).2 in 55 and (0).2 in 116
  have eq378 (X0 X1 : G) : (X1 ◇ sK2) ≠ (sK1 ◇ X0) := superpose eq323 eq287 -- superposition 287,323, 323 into 287, unify on (0).2 in 323 and (0).1 in 287
  subsumption eq378 rfl


@[equational_result]
theorem Equation3551_implies_Equation4157 (G : Type*) [Magma G] (h : Equation3551 G) : Equation4157 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ X3) = (X3 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.1 in 11
  have eq19 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.2 in 12
  have eq36 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) ◇ X4) = (X4 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3))))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq42 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq9 eq32 -- forward demodulation 32,9
  have eq45 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ X3) := superpose eq42 eq19 -- backward demodulation 19,42
  have eq55 (X0 X2 : G) : (X0 ◇ X2) = (X2 ◇ (X0 ◇ X0)) := superpose eq42 eq33 -- forward demodulation 33,42
  have eq60 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) ◇ X4) = (X4 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3))))) := superpose eq42 eq36 -- forward demodulation 36,42
  have eq61 (X0 X1 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X4 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X3))))) := superpose eq42 eq60 -- forward demodulation 60,42
  have eq62 (X0 X1 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X4 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq45 eq61 -- forward demodulation 61,45
  have eq63 (X1 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X1 ◇ X4) := superpose eq45 eq62 -- forward demodulation 62,45
  have eq99 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq42 eq42 -- superposition 42,42, 42 into 42, unify on (0).2 in 42 and (0).2.1 in 42
  have eq100 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ ((X2 ◇ X3) ◇ X2)) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).2 in 42
  have eq105 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq42 eq10 -- superposition 10,42, 42 into 10, unify on (0).2 in 42 and (0).2 in 10
  have eq120 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq63 eq99 -- forward demodulation 99,63
  have eq124 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq120 eq11 -- backward demodulation 11,120
  have eq128 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq124 eq100 -- forward demodulation 100,124
  have eq129 (X0 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X0)) := superpose eq120 eq128 -- forward demodulation 128,120
  have eq248 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq55 eq129 -- superposition 129,55, 55 into 129, unify on (0).2 in 55 and (0).2 in 129
  have eq308 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq248 eq105 -- superposition 105,248, 248 into 105, unify on (0).2 in 248 and (0).2 in 105
  subsumption eq308 rfl


@[equational_result]
theorem Equation3551_implies_Equation4007 (G : Type*) [Magma G] (h : Equation3551 G) : Equation4007 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK2) := mod_symm nh
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
  have eq78 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq55 eq55 -- superposition 55,55, 55 into 55, unify on (0).2 in 55 and (0).2.2 in 55
  have eq87 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose eq45 eq78 -- forward demodulation 78,45
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq42 eq42 -- superposition 42,42, 42 into 42, unify on (0).2 in 42 and (0).2.1 in 42
  have eq102 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ ((X2 ◇ X3) ◇ X2)) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).2 in 42
  have eq121 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq61 eq101 -- forward demodulation 101,61
  have eq124 (X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ X2) ◇ X3) := superpose eq121 eq49 -- backward demodulation 49,121
  have eq125 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq121 eq11 -- backward demodulation 11,121
  have eq128 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK2) := superpose eq125 eq10 -- backward demodulation 10,125
  have eq129 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq125 eq102 -- forward demodulation 102,125
  have eq130 (X0 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X0)) := superpose eq121 eq129 -- forward demodulation 129,121
  have eq141 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ X2) := superpose eq55 eq125 -- superposition 125,55, 55 into 125, unify on (0).2 in 55 and (0).2.2 in 125
  have eq144 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = (X1 ◇ X2) := superpose eq87 eq141 -- forward demodulation 141,87
  have eq184 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X2) := superpose eq124 eq121 -- superposition 121,124, 124 into 121, unify on (0).2 in 124 and (0).2 in 121
  have eq206 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq55 eq130 -- superposition 130,55, 55 into 130, unify on (0).2 in 55 and (0).2 in 130
  have eq290 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (X3 ◇ (X1 ◇ X2)) := superpose eq184 eq144 -- superposition 144,184, 184 into 144, unify on (0).2 in 184 and (0).1 in 144
  have eq337 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK2)) := superpose eq206 eq128 -- superposition 128,206, 206 into 128, unify on (0).2 in 206 and (0).2 in 128
  subsumption eq337 eq290


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
theorem Equation3551_implies_Equation3269 (G : Type*) [Magma G] (h : Equation3551 G) : Equation3269 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ X3) = (X3 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.1 in 11
  have eq14 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (X3 ◇ ((X2 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.1 in 11
  have eq19 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq20 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq11 eq14 -- forward demodulation 14,11
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq35 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) ◇ X4) = (X4 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2.1 in 11
  have eq42 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq9 eq32 -- forward demodulation 32,9
  have eq45 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ X3) := superpose eq42 eq19 -- backward demodulation 19,42
  have eq49 (X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (X2 ◇ X3) := superpose eq45 eq20 -- backward demodulation 20,45
  have eq58 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X4 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (X1 ◇ (X1 ◇ X3)))) := superpose eq42 eq35 -- forward demodulation 35,42
  have eq59 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X4 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0))) := superpose eq45 eq58 -- forward demodulation 58,45
  have eq60 (X0 X1 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X4 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq42 eq59 -- forward demodulation 59,42
  have eq61 (X1 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = (X1 ◇ X4) := superpose eq45 eq60 -- forward demodulation 60,45
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq42 eq42 -- superposition 42,42, 42 into 42, unify on (0).2 in 42 and (0).2.1 in 42
  have eq121 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq61 eq101 -- forward demodulation 101,61
  have eq124 (X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ X2) ◇ X3) := superpose eq121 eq49 -- backward demodulation 49,121
  have eq125 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq121 eq11 -- backward demodulation 11,121
  have eq128 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq125 eq10 -- backward demodulation 10,125
  have eq184 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X2) := superpose eq124 eq121 -- superposition 121,124, 124 into 121, unify on (0).2 in 124 and (0).2 in 121
  have eq200 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X1 ◇ X2)) := superpose eq125 eq184 -- superposition 184,125, 125 into 184, unify on (0).2 in 125 and (0).1 in 184
  have eq224 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ sK0)) := superpose eq184 eq128 -- superposition 128,184, 184 into 128, unify on (0).2 in 184 and (0).2.2 in 128
  subsumption eq224 eq200


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
theorem Equation3358_implies_Equation4113 (G : Type*) [Magma G] (h : Equation3358 G) : Equation4113 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK3) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X3 ◇ (X3 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK0) ≠ ((sK3 ◇ (sK2 ◇ sK3)) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq18 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq25 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq30 (X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X2 ◇ X3)) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq31 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ X0) := superpose eq30 eq12 -- backward demodulation 12,30
  have eq33 : (sK0 ◇ sK0) ≠ ((sK2 ◇ sK3) ◇ sK1) := superpose eq30 eq14 -- backward demodulation 14,30
  have eq35 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq18 -- forward demodulation 18,13
  have eq36 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq30 eq35 -- forward demodulation 35,30
  have eq44 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq30 eq25 -- forward demodulation 25,30
  have eq45 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ X1) := superpose eq36 eq44 -- forward demodulation 44,36
  have eq48 (X0 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X2) ◇ X3) := superpose eq45 eq13 -- backward demodulation 13,45
  have eq49 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq45 eq9 -- backward demodulation 9,45
  have eq67 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq31 eq48 -- superposition 48,31, 31 into 48, unify on (0).2 in 31 and (0).2 in 48
  have eq92 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK1) := superpose eq67 eq33 -- superposition 33,67, 67 into 33, unify on (0).2 in 67 and (0).2 in 33
  have eq112 (X0 X1 : G) : (X0 ◇ sK0) ≠ (X1 ◇ sK1) := superpose eq67 eq92 -- superposition 92,67, 67 into 92, unify on (0).2 in 67 and (0).1 in 92
  have eq150 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq49 eq45 -- superposition 45,49, 49 into 45, unify on (0).2 in 49 and (0).1 in 45
  have eq173 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X1) := superpose eq67 eq150 -- superposition 150,67, 67 into 150, unify on (0).2 in 67 and (0).1 in 150
  have eq256 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq173 eq173 -- superposition 173,173, 173 into 173, unify on (0).2 in 173 and (0).1 in 173
  have eq290 (X0 X1 X2 : G) : (X1 ◇ X0) ≠ (X2 ◇ sK1) := superpose eq173 eq112 -- superposition 112,173, 173 into 112, unify on (0).2 in 173 and (0).1 in 112
  subsumption eq290 eq256


@[equational_result]
theorem Equation3358_implies_Equation4082 (G : Type*) [Magma G] (h : Equation3358 G) : Equation4082 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X3 ◇ (X3 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq18 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq24 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq28 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X3) = (X3 ◇ (X3 ◇ ((X2 ◇ X1) ◇ X0))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2.2 in 9
  have eq30 (X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X2 ◇ X3)) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq31 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ X0) := superpose eq30 eq12 -- backward demodulation 12,30
  have eq33 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq30 eq14 -- backward demodulation 14,30
  have eq35 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq18 -- forward demodulation 18,13
  have eq36 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq30 eq35 -- forward demodulation 35,30
  have eq43 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq30 eq24 -- forward demodulation 24,30
  have eq44 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ X1) := superpose eq36 eq43 -- forward demodulation 43,36
  have eq47 (X0 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X2) ◇ X3) := superpose eq44 eq13 -- backward demodulation 13,44
  have eq51 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = (X3 ◇ (X3 ◇ X0)) := superpose eq44 eq28 -- forward demodulation 28,44
  have eq52 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = (X3 ◇ X0) := superpose eq44 eq51 -- forward demodulation 51,44
  have eq67 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq31 eq47 -- superposition 47,31, 31 into 47, unify on (0).2 in 31 and (0).2 in 47
  have eq183 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK0) := superpose eq52 eq33 -- superposition 33,52, 52 into 33, unify on (0).2 in 52 and (0).2 in 33
  subsumption eq183 eq67


@[equational_result]
theorem Equation3358_implies_Equation3865 (G : Type*) [Magma G] (h : Equation3358 G) : Equation3865 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X3 ◇ (X3 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq16 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq24 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq27 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X3) = (X3 ◇ (X3 ◇ ((X2 ◇ X1) ◇ X0))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2.2 in 9
  have eq29 (X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X2 ◇ X3)) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq30 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ X0) := superpose eq29 eq12 -- backward demodulation 12,29
  have eq33 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq34 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq29 eq33 -- forward demodulation 33,29
  have eq42 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq29 eq24 -- forward demodulation 24,29
  have eq43 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ X1) := superpose eq34 eq42 -- forward demodulation 42,34
  have eq46 (X0 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X2) ◇ X3) := superpose eq43 eq13 -- backward demodulation 13,43
  have eq48 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq43 eq10 -- backward demodulation 10,43
  have eq50 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = (X3 ◇ (X3 ◇ X0)) := superpose eq43 eq27 -- forward demodulation 27,43
  have eq51 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = (X3 ◇ X0) := superpose eq43 eq50 -- forward demodulation 50,43
  have eq66 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq30 eq46 -- superposition 46,30, 30 into 46, unify on (0).2 in 30 and (0).2 in 46
  have eq72 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK1) := superpose eq46 eq48 -- superposition 48,46, 46 into 48, unify on (0).2 in 46 and (0).2 in 48
  have eq93 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK1) := superpose eq66 eq72 -- superposition 72,66, 66 into 72, unify on (0).2 in 66 and (0).2 in 72
  have eq107 (X0 X1 : G) : (X0 ◇ sK0) ≠ (X1 ◇ sK1) := superpose eq66 eq93 -- superposition 93,66, 66 into 93, unify on (0).2 in 66 and (0).1 in 93
  have eq178 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X2) := superpose eq46 eq51 -- superposition 51,46, 46 into 51, unify on (0).2 in 46 and (0).1 in 51
  have eq290 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq178 eq178 -- superposition 178,178, 178 into 178, unify on (0).2 in 178 and (0).1 in 178
  have eq332 (X0 X1 X2 : G) : (X1 ◇ X0) ≠ (X2 ◇ sK1) := superpose eq178 eq107 -- superposition 107,178, 178 into 107, unify on (0).2 in 178 and (0).1 in 107
  subsumption eq332 eq290


@[equational_result]
theorem Equation3358_implies_Equation3924 (G : Type*) [Magma G] (h : Equation3358 G) : Equation3924 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X3 ◇ (X3 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq17 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq18 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq24 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq29 (X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X2 ◇ X3)) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq30 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ X0) := superpose eq29 eq12 -- backward demodulation 12,29
  have eq33 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq18 -- forward demodulation 18,13
  have eq34 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq29 eq33 -- forward demodulation 33,29
  have eq41 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq29 eq24 -- forward demodulation 24,29
  have eq42 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ X1) := superpose eq34 eq41 -- forward demodulation 41,34
  have eq45 (X0 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X2) ◇ X3) := superpose eq42 eq13 -- backward demodulation 13,42
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq42 eq9 -- backward demodulation 9,42
  have eq63 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq30 eq45 -- superposition 45,30, 30 into 45, unify on (0).2 in 30 and (0).2 in 45
  have eq89 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK1) := superpose eq63 eq14 -- superposition 14,63, 63 into 14, unify on (0).2 in 63 and (0).1 in 14
  have eq97 (X0 X1 : G) : (X0 ◇ sK0) ≠ (X1 ◇ sK1) := superpose eq63 eq89 -- superposition 89,63, 63 into 89, unify on (0).2 in 63 and (0).1 in 89
  have eq134 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq46 eq42 -- superposition 42,46, 46 into 42, unify on (0).2 in 46 and (0).1 in 42
  have eq154 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X1) := superpose eq63 eq134 -- superposition 134,63, 63 into 134, unify on (0).2 in 63 and (0).1 in 134
  have eq230 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq154 eq154 -- superposition 154,154, 154 into 154, unify on (0).2 in 154 and (0).1 in 154
  have eq264 (X0 X1 X2 : G) : (X1 ◇ X0) ≠ (X2 ◇ sK1) := superpose eq154 eq97 -- superposition 97,154, 154 into 97, unify on (0).2 in 154 and (0).1 in 97
  subsumption eq264 eq230


@[equational_result]
theorem Equation3358_implies_Equation4226 (G : Type*) [Magma G] (h : Equation3358 G) : Equation4226 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK2) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X3 ◇ (X3 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq13


@[equational_result]
theorem Equation3358_implies_Equation3322 (G : Type*) [Magma G] (h : Equation3358 G) : Equation3322 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X3 ◇ (X3 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq16 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq28 (X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X2 ◇ X3)) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq29 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ X0) := superpose eq28 eq12 -- backward demodulation 12,28
  have eq31 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK1)) := superpose eq28 eq10 -- backward demodulation 10,28
  have eq33 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq34 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq28 eq33 -- forward demodulation 33,28
  have eq41 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq28 eq23 -- forward demodulation 23,28
  have eq42 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ X1) := superpose eq34 eq41 -- forward demodulation 41,34
  have eq45 (X0 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X2) ◇ X3) := superpose eq42 eq13 -- backward demodulation 13,42
  have eq63 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq29 eq45 -- superposition 45,29, 29 into 45, unify on (0).2 in 29 and (0).2 in 45
  have eq90 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq63 eq31 -- superposition 31,63, 63 into 31, unify on (0).2 in 63 and (0).2.2 in 31
  subsumption eq90 eq42


@[equational_result]
theorem Equation3358_implies_Equation4103 (G : Type*) [Magma G] (h : Equation3358 G) : Equation4103 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X3 ◇ (X3 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK3) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq18 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq25 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq30 (X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X2 ◇ X3)) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq31 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ X0) := superpose eq30 eq12 -- backward demodulation 12,30
  have eq33 : (sK0 ◇ sK0) ≠ ((sK2 ◇ sK0) ◇ sK3) := superpose eq30 eq14 -- backward demodulation 14,30
  have eq35 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq18 -- forward demodulation 18,13
  have eq36 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq30 eq35 -- forward demodulation 35,30
  have eq44 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq30 eq25 -- forward demodulation 25,30
  have eq45 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ X1) := superpose eq36 eq44 -- forward demodulation 44,36
  have eq48 (X0 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X2) ◇ X3) := superpose eq45 eq13 -- backward demodulation 13,45
  have eq49 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq45 eq9 -- backward demodulation 9,45
  have eq67 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq31 eq48 -- superposition 48,31, 31 into 48, unify on (0).2 in 31 and (0).2 in 48
  have eq92 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK3) := superpose eq67 eq33 -- superposition 33,67, 67 into 33, unify on (0).2 in 67 and (0).2 in 33
  have eq112 (X0 X1 : G) : (X0 ◇ sK0) ≠ (X1 ◇ sK3) := superpose eq67 eq92 -- superposition 92,67, 67 into 92, unify on (0).2 in 67 and (0).1 in 92
  have eq150 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq49 eq45 -- superposition 45,49, 49 into 45, unify on (0).2 in 49 and (0).1 in 45
  have eq172 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X1) := superpose eq67 eq150 -- superposition 150,67, 67 into 150, unify on (0).2 in 67 and (0).1 in 150
  have eq248 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq172 eq172 -- superposition 172,172, 172 into 172, unify on (0).2 in 172 and (0).1 in 172
  have eq282 (X0 X1 X2 : G) : (X1 ◇ X0) ≠ (X2 ◇ sK3) := superpose eq172 eq112 -- superposition 112,172, 172 into 112, unify on (0).2 in 172 and (0).1 in 112
  subsumption eq282 eq248


@[equational_result]
theorem Equation3358_implies_Equation3475 (G : Type*) [Magma G] (h : Equation3358 G) : Equation3475 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X3 ◇ (X3 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2 in 14
  have eq18 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq19 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq25 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq30 (X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X2 ◇ X3)) := superpose eq13 eq18 -- forward demodulation 18,13
  have eq31 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ X0) := superpose eq30 eq12 -- backward demodulation 12,30
  have eq35 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq19 -- forward demodulation 19,13
  have eq36 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq30 eq35 -- forward demodulation 35,30
  have eq43 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq30 eq25 -- forward demodulation 25,30
  have eq44 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ X1) := superpose eq36 eq43 -- forward demodulation 43,36
  have eq47 (X0 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X2) ◇ X3) := superpose eq44 eq13 -- backward demodulation 13,44
  have eq48 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq44 eq9 -- backward demodulation 9,44
  have eq66 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq31 eq47 -- superposition 47,31, 31 into 47, unify on (0).2 in 31 and (0).2 in 47
  have eq94 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK1) := superpose eq66 eq15 -- superposition 15,66, 66 into 15, unify on (0).2 in 66 and (0).2 in 15
  have eq104 (X0 X1 : G) : (X0 ◇ sK0) ≠ (X1 ◇ sK1) := superpose eq66 eq94 -- superposition 94,66, 66 into 94, unify on (0).2 in 66 and (0).1 in 94
  have eq142 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq48 eq44 -- superposition 44,48, 48 into 44, unify on (0).2 in 48 and (0).1 in 44
  have eq163 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X1) := superpose eq66 eq142 -- superposition 142,66, 66 into 142, unify on (0).2 in 66 and (0).1 in 142
  have eq239 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq163 eq163 -- superposition 163,163, 163 into 163, unify on (0).2 in 163 and (0).1 in 163
  have eq278 (X0 X1 X2 : G) : (X1 ◇ X0) ≠ (X2 ◇ sK1) := superpose eq163 eq104 -- superposition 104,163, 163 into 104, unify on (0).2 in 163 and (0).1 in 104
  subsumption eq278 eq239


@[equational_result]
theorem Equation3358_implies_Equation4088 (G : Type*) [Magma G] (h : Equation3358 G) : Equation4088 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK0) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X3 ◇ (X3 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK0) ≠ ((sK2 ◇ (sK0 ◇ sK2)) ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq18 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq25 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq30 (X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X2 ◇ X3)) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq31 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ X0) := superpose eq30 eq12 -- backward demodulation 12,30
  have eq33 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK2) ◇ sK2) := superpose eq30 eq14 -- backward demodulation 14,30
  have eq35 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq18 -- forward demodulation 18,13
  have eq36 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq30 eq35 -- forward demodulation 35,30
  have eq44 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq30 eq25 -- forward demodulation 25,30
  have eq45 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ X1) := superpose eq36 eq44 -- forward demodulation 44,36
  have eq48 (X0 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X2) ◇ X3) := superpose eq45 eq13 -- backward demodulation 13,45
  have eq49 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq45 eq9 -- backward demodulation 9,45
  have eq67 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq31 eq48 -- superposition 48,31, 31 into 48, unify on (0).2 in 31 and (0).2 in 48
  have eq73 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK2) := superpose eq48 eq33 -- superposition 33,48, 48 into 33, unify on (0).2 in 48 and (0).2 in 33
  have eq94 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK2) := superpose eq67 eq73 -- superposition 73,67, 67 into 73, unify on (0).2 in 67 and (0).2 in 73
  have eq113 (X0 X1 : G) : (X0 ◇ sK0) ≠ (X1 ◇ sK2) := superpose eq67 eq94 -- superposition 94,67, 67 into 94, unify on (0).2 in 67 and (0).1 in 94
  have eq151 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq49 eq45 -- superposition 45,49, 49 into 45, unify on (0).2 in 49 and (0).1 in 45
  have eq172 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X1) := superpose eq67 eq151 -- superposition 151,67, 67 into 151, unify on (0).2 in 67 and (0).1 in 151
  have eq251 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq172 eq172 -- superposition 172,172, 172 into 172, unify on (0).2 in 172 and (0).1 in 172
  have eq290 (X0 X1 X2 : G) : (X1 ◇ X0) ≠ (X2 ◇ sK2) := superpose eq172 eq113 -- superposition 113,172, 172 into 113, unify on (0).2 in 172 and (0).1 in 113
  subsumption eq290 eq251


@[equational_result]
theorem Equation3358_implies_Equation3893 (G : Type*) [Magma G] (h : Equation3358 G) : Equation3893 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X3 ◇ (X3 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq16 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq24 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq29 (X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X2 ◇ X3)) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq30 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ X0) := superpose eq29 eq12 -- backward demodulation 12,29
  have eq33 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq34 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq29 eq33 -- forward demodulation 33,29
  have eq42 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq29 eq24 -- forward demodulation 24,29
  have eq43 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ X1) := superpose eq34 eq42 -- forward demodulation 42,34
  have eq46 (X0 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X2) ◇ X3) := superpose eq43 eq13 -- backward demodulation 13,43
  have eq48 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ sK0) := superpose eq43 eq10 -- backward demodulation 10,43
  have eq66 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq30 eq46 -- superposition 46,30, 30 into 46, unify on (0).2 in 30 and (0).2 in 46
  have eq68 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq46 eq48 -- superposition 48,46, 46 into 48, unify on (0).2 in 46 and (0).2 in 48
  subsumption eq68 eq66


@[equational_result]
theorem Equation3358_implies_Equation3522 (G : Type*) [Magma G] (h : Equation3358 G) : Equation3522 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X3 ◇ (X3 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq18 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq24 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq29 (X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X2 ◇ X3)) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq30 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ X0) := superpose eq29 eq12 -- backward demodulation 12,29
  have eq32 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq29 eq14 -- backward demodulation 14,29
  have eq34 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq18 -- forward demodulation 18,13
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq29 eq34 -- forward demodulation 34,29
  have eq42 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq29 eq24 -- forward demodulation 24,29
  have eq43 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ X1) := superpose eq35 eq42 -- forward demodulation 42,35
  have eq46 (X0 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X2) ◇ X3) := superpose eq43 eq13 -- backward demodulation 13,43
  have eq64 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq30 eq46 -- superposition 46,30, 30 into 46, unify on (0).2 in 30 and (0).2 in 46
  have eq91 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq64 eq32 -- superposition 32,64, 64 into 32, unify on (0).2 in 64 and (0).2.2 in 32
  subsumption eq91 eq43


@[equational_result]
theorem Equation3358_implies_Equation3533 (G : Type*) [Magma G] (h : Equation3358 G) : Equation3533 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X3 ◇ (X3 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq18 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq24 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq29 (X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X2 ◇ X3)) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq30 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ X0) := superpose eq29 eq12 -- backward demodulation 12,29
  have eq32 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq29 eq14 -- backward demodulation 14,29
  have eq34 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq18 -- forward demodulation 18,13
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq29 eq34 -- forward demodulation 34,29
  have eq42 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq29 eq24 -- forward demodulation 24,29
  have eq43 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ X1) := superpose eq35 eq42 -- forward demodulation 42,35
  have eq46 (X0 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X2) ◇ X3) := superpose eq43 eq13 -- backward demodulation 13,43
  have eq64 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq30 eq46 -- superposition 46,30, 30 into 46, unify on (0).2 in 30 and (0).2 in 46
  have eq91 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq64 eq32 -- superposition 32,64, 64 into 32, unify on (0).2 in 64 and (0).2.2 in 32
  subsumption eq91 eq43


@[equational_result]
theorem Equation3358_implies_Equation3744 (G : Type*) [Magma G] (h : Equation3358 G) : Equation3744 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ (sK3 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X3 ◇ (X3 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq16 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = ((X2 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq28 (X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X2 ◇ X3)) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq32 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq33 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq28 eq32 -- forward demodulation 32,28
  have eq40 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq28 eq23 -- forward demodulation 23,28
  have eq41 (X0 X1 X3 : G) : (X3 ◇ X1) = (X3 ◇ (X0 ◇ X1)) := superpose eq33 eq40 -- forward demodulation 40,33
  have eq44 (X0 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X2) ◇ X3) := superpose eq41 eq13 -- backward demodulation 13,41
  have eq65 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK3 ◇ sK1)) := superpose eq44 eq10 -- superposition 10,44, 44 into 10, unify on (0).2 in 44 and (0).2 in 10
  subsumption eq65 eq41


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


