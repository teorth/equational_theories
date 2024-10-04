import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation4514_implies_Equation4518 (G : Type*) [Magma G] (h : Equation4514 G) : Equation4518 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK3) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK3)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq39 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK2)) ≠ (sK0 ◇ (X1 ◇ sK3)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1 in 16
  have eq50 (X1 : G) : ((sK0 ◇ sK2) ◇ sK0) ≠ (sK0 ◇ (X1 ◇ sK3)) := superpose eq9 eq39 -- superposition 39,9, 9 into 39, unify on (0).2 in 9 and (0).1 in 39
  have eq77 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq95 (X0 X1 : G) : ((sK0 ◇ sK2) ◇ sK0) ≠ (sK0 ◇ (sK3 ◇ (X1 ◇ X0))) := superpose eq9 eq50 -- superposition 50,9, 9 into 50, unify on (0).2 in 9 and (0).2.2 in 50
  subsumption eq95 eq77


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
theorem Equation4517_implies_Equation4404 (G : Type*) [Magma G] (h : Equation4517 G) : Equation4404 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X3) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK2) ◇ sK3) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X2) ◇ X5) = (X4 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = (X0 ◇ (X4 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).1 in 10
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X3 ◇ X1))) = (X4 ◇ (X5 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.2 in 17
  have eq70 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq244 (X0 X2 X3 X4 X5 : G) : (sK0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ≠ (sK0 ◇ (X5 ◇ sK1)) := superpose eq12 eq70 -- superposition 70,12, 12 into 70, unify on (0).2 in 12 and (0).1.2 in 70
  subsumption eq244 eq51


@[equational_result]
theorem Equation4517_implies_Equation4441 (G : Type*) [Magma G] (h : Equation4517 G) : Equation4441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X3) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK2) ◇ sK3) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X2) ◇ X5) = (X4 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = (X0 ◇ (X4 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).1 in 10
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X3 ◇ X1))) = (X4 ◇ (X5 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.2 in 17
  have eq77 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq244 (X0 X2 X3 X4 X5 : G) : (sK0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ≠ (sK0 ◇ (X5 ◇ sK0)) := superpose eq12 eq77 -- superposition 77,12, 12 into 77, unify on (0).2 in 12 and (0).1.2 in 77
  subsumption eq244 eq51


@[equational_result]
theorem Equation4517_implies_Equation4478 (G : Type*) [Magma G] (h : Equation4517 G) : Equation4478 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X3) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK2) ◇ sK3) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X2) ◇ X5) = (X4 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = (X0 ◇ (X4 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).1 in 10
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X3 ◇ X1))) = (X4 ◇ (X5 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.2 in 17
  have eq77 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq244 (X0 X2 X3 X4 X5 : G) : (sK0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ≠ (sK0 ◇ (X5 ◇ sK1)) := superpose eq12 eq77 -- superposition 77,12, 12 into 77, unify on (0).2 in 12 and (0).1.2 in 77
  subsumption eq244 eq51


@[equational_result]
theorem Equation4517_implies_Equation4509 (G : Type*) [Magma G] (h : Equation4517 G) : Equation4509 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK0) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X2) ◇ X5) = (X4 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = (X0 ◇ (X4 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X3 ◇ X1))) = (X4 ◇ (X5 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.2 in 17
  have eq77 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq244 (X0 X2 X3 X4 X5 : G) : (sK0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ≠ (sK0 ◇ (X5 ◇ sK2)) := superpose eq12 eq77 -- superposition 77,12, 12 into 77, unify on (0).2 in 12 and (0).1.2 in 77
  subsumption eq244 eq51


@[equational_result]
theorem Equation4517_implies_Equation4513 (G : Type*) [Magma G] (h : Equation4517 G) : Equation4513 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK1) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X2) ◇ X5) = (X4 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = (X0 ◇ (X4 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X3 ◇ X1))) = (X4 ◇ (X5 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.2 in 17
  have eq77 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq244 (X0 X2 X3 X4 X5 : G) : (sK0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ≠ (sK0 ◇ (X5 ◇ sK2)) := superpose eq12 eq77 -- superposition 77,12, 12 into 77, unify on (0).2 in 12 and (0).1.2 in 77
  subsumption eq244 eq51


@[equational_result]
theorem Equation4517_implies_Equation4518 (G : Type*) [Magma G] (h : Equation4517 G) : Equation4518 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK3) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X2) ◇ X5) = (X4 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = (X0 ◇ (X4 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK3)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X3 ◇ X1))) = (X4 ◇ (X5 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.2 in 17
  have eq77 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK3)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq244 (X0 X2 X3 X4 X5 : G) : (sK0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ≠ (sK0 ◇ (X5 ◇ sK2)) := superpose eq12 eq77 -- superposition 77,12, 12 into 77, unify on (0).2 in 12 and (0).1.2 in 77
  subsumption eq244 eq51


@[equational_result]
theorem Equation4517_implies_Equation4519 (G : Type*) [Magma G] (h : Equation4517 G) : Equation4519 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK3) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X2) ◇ X5) = (X4 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = (X0 ◇ (X4 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK3)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X3 ◇ X1))) = (X4 ◇ (X5 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.2 in 17
  have eq77 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK3)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq244 (X0 X2 X3 X4 X5 : G) : (sK0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ≠ (sK0 ◇ (X5 ◇ sK2)) := superpose eq12 eq77 -- superposition 77,12, 12 into 77, unify on (0).2 in 12 and (0).1.2 in 77
  subsumption eq244 eq51


@[equational_result]
theorem Equation4517_implies_Equation4520 (G : Type*) [Magma G] (h : Equation4517 G) : Equation4520 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X2) ◇ X5) = (X4 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = (X0 ◇ (X4 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK3)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X3 ◇ X1))) = (X4 ◇ (X5 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.2 in 17
  have eq77 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK3)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq244 (X0 X2 X3 X4 X5 : G) : (sK0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ≠ (sK0 ◇ (X5 ◇ sK2)) := superpose eq12 eq77 -- superposition 77,12, 12 into 77, unify on (0).2 in 12 and (0).1.2 in 77
  subsumption eq244 eq51


@[equational_result]
theorem Equation4517_implies_Equation4521 (G : Type*) [Magma G] (h : Equation4517 G) : Equation4521 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK3) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X2) ◇ X5) = (X4 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = (X0 ◇ (X4 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK3)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X3 ◇ X1))) = (X4 ◇ (X5 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.2 in 17
  have eq71 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK3)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq244 (X0 X2 X3 X4 X5 : G) : (sK0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ≠ (sK0 ◇ (X5 ◇ sK2)) := superpose eq12 eq71 -- superposition 71,12, 12 into 71, unify on (0).2 in 12 and (0).1.2 in 71
  subsumption eq244 eq51


@[equational_result]
theorem Equation4517_implies_Equation4522 (G : Type*) [Magma G] (h : Equation4517 G) : Equation4522 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK3) ◇ sK4) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X2) ◇ X5) = (X4 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = (X0 ◇ (X4 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK3)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X3 ◇ X1))) = (X4 ◇ (X5 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.2 in 17
  have eq77 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK3)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq244 (X0 X2 X3 X4 X5 : G) : (sK0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ≠ (sK0 ◇ (X5 ◇ sK2)) := superpose eq12 eq77 -- superposition 77,12, 12 into 77, unify on (0).2 in 12 and (0).1.2 in 77
  subsumption eq244 eq51


@[equational_result]
theorem Equation4523_implies_Equation4540 (G : Type*) [Magma G] (h : Equation4523 G) : Equation4540 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X3) = (X3 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X3)) = ((X1 ◇ (X0 ◇ X2)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq67 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq123 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ X0) = (((X2 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) ◇ X0) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2 in 12
  have eq153 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ X0) = ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) := superpose eq9 eq123 -- forward demodulation 123,9
  have eq154 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X0) = (((X2 ◇ X3) ◇ X0) ◇ X0) := superpose eq67 eq153 -- forward demodulation 153,67
  have eq190 (X0 X1 X3 : G) : ((X0 ◇ (X1 ◇ X3)) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1 in 14
  have eq252 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X3)) ◇ X0) := superpose eq154 eq190 -- forward demodulation 190,154
  have eq253 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq252 eq14 -- backward demodulation 14,252
  have eq352 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq11 eq253 -- superposition 253,11, 11 into 253, unify on (0).2 in 11 and (0).2 in 253
  have eq515 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ X1) := superpose eq9 eq352 -- superposition 352,9, 9 into 352, unify on (0).2 in 9 and (0).1 in 352
  have eq551 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq352 eq10 -- superposition 10,352, 352 into 10, unify on (0).2 in 352 and (0).2 in 10
  subsumption eq551 eq515


@[equational_result]
theorem Equation4524_implies_Equation4532 (G : Type*) [Magma G] (h : Equation4524 G) : Equation4532 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X0) = (X3 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq72 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).2 in 11
  have eq75 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X1) = (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq98 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X0) = ((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X1) := superpose eq72 eq75 -- forward demodulation 75,72
  have eq99 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ X0) := superpose eq72 eq98 -- forward demodulation 98,72
  have eq1349 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X0) = ((X0 ◇ X2) ◇ X0) := superpose eq99 eq99 -- superposition 99,99, 99 into 99, unify on (0).2 in 99 and (0).1 in 99
  have eq1757 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X0) = (X1 ◇ (X0 ◇ X2)) := superpose eq9 eq1349 -- superposition 1349,9, 9 into 1349, unify on (0).2 in 9 and (0).1 in 1349
  have eq1814 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ X0) ◇ sK1) := superpose eq1349 eq10 -- superposition 10,1349, 1349 into 10, unify on (0).2 in 1349 and (0).2 in 10
  subsumption eq1814 eq1757


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
theorem Equation4527_implies_Equation4572 (G : Type*) [Magma G] (h : Equation4527 G) : Equation4572 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK3) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq226 (X0 X1 X2 X4 : G) : (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) = (X0 ◇ (X1 ◇ X4)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2 in 12
  have eq276 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ sK0) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2 in 18
  subsumption eq276 eq226


@[equational_result]
theorem Equation453_implies_Equation1466 (G : Type*) [Magma G] (h : Equation453 G) : Equation1466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq18 : sK0 ≠ (sK0 ◇ sK2) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation453_implies_Equation2085 (G : Type*) [Magma G] (h : Equation453 G) : Equation2085 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq17 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK3 ◇ sK3)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK3) := superpose eq14 eq17 -- forward demodulation 17,14
  have eq19 : sK0 ≠ (sK0 ◇ sK3) := superpose eq14 eq18 -- forward demodulation 18,14
  subsumption eq19 eq14


@[equational_result]
theorem Equation4532_implies_Equation4560 (G : Type*) [Magma G] (h : Equation4532 G) : Equation4560 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK0) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (X3 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X1)) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK3 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq36 (X0 X1 : G) : (X1 ◇ (sK3 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).1 in 16
  have eq44 (X1 : G) : ((sK3 ◇ sK0) ◇ sK3) ≠ (X1 ◇ (sK1 ◇ sK2)) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).1 in 36
  have eq122 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X3) ◇ X2) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq131 (X0 X1 : G) : ((sK3 ◇ sK0) ◇ sK3) ≠ ((X0 ◇ X1) ◇ X0) := superpose eq17 eq44 -- superposition 44,17, 17 into 44, unify on (0).2 in 17 and (0).2 in 44
  subsumption eq131 eq122


@[equational_result]
theorem Equation4532_implies_Equation4565 (G : Type*) [Magma G] (h : Equation4532 G) : Equation4565 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK1) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (X3 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X1)) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK3 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq36 (X0 X1 : G) : (X1 ◇ (sK3 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).1 in 16
  have eq44 (X1 : G) : ((sK3 ◇ sK1) ◇ sK3) ≠ (X1 ◇ (sK1 ◇ sK2)) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).1 in 36
  have eq122 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X3) ◇ X2) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq131 (X0 X1 : G) : ((sK3 ◇ sK1) ◇ sK3) ≠ ((X0 ◇ X1) ◇ X0) := superpose eq17 eq44 -- superposition 44,17, 17 into 44, unify on (0).2 in 17 and (0).2 in 44
  subsumption eq131 eq122


@[equational_result]
theorem Equation4535_implies_Equation4552 (G : Type*) [Magma G] (h : Equation4535 G) : Equation4552 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK3) ◇ sK0) := mod_symm nh
  have eq15 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = (((X1 ◇ X3) ◇ X0) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ X3)) = (X2 ◇ (X0 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ ((X0 ◇ X2) ◇ sK2)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.2 in 19
  have eq208 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X5)) = (X3 ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq268 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2 in 20
  subsumption eq268 eq208


@[equational_result]
theorem Equation4535_implies_Equation4577 (G : Type*) [Magma G] (h : Equation4535 G) : Equation4577 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK4) ◇ sK0) := mod_symm nh
  have eq15 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = (((X1 ◇ X3) ◇ X0) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ X3)) = (X2 ◇ (X0 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ ((X0 ◇ X2) ◇ sK3)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.2 in 19
  have eq208 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X5)) = (X3 ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq268 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2 in 20
  subsumption eq268 eq208


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
theorem Equation4540_implies_Equation4415 (G : Type*) [Magma G] (h : Equation4540 G) : Equation4415 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK2 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X3) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).1 in 10
  have eq36 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK1)) ≠ (sK0 ◇ (X1 ◇ sK2)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1 in 16
  have eq50 (X1 : G) : ((sK1 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (X1 ◇ sK2)) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).1 in 36
  have eq77 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq95 (X0 X1 : G) : ((sK1 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (sK2 ◇ (X1 ◇ X0))) := superpose eq9 eq50 -- superposition 50,9, 9 into 50, unify on (0).2 in 9 and (0).2.2 in 50
  subsumption eq95 eq77


@[equational_result]
theorem Equation4540_implies_Equation4452 (G : Type*) [Magma G] (h : Equation4540 G) : Equation4452 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK2 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X3) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).1 in 10
  have eq36 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK0)) ≠ (sK0 ◇ (X1 ◇ sK2)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1 in 16
  have eq50 (X1 : G) : ((sK0 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (X1 ◇ sK2)) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).1 in 36
  have eq77 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq95 (X0 X1 : G) : ((sK0 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (sK2 ◇ (X1 ◇ X0))) := superpose eq9 eq50 -- superposition 50,9, 9 into 50, unify on (0).2 in 9 and (0).2.2 in 50
  subsumption eq95 eq77


@[equational_result]
theorem Equation4540_implies_Equation4489 (G : Type*) [Magma G] (h : Equation4540 G) : Equation4489 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK2 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X3) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).1 in 10
  have eq36 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK1)) ≠ (sK0 ◇ (X1 ◇ sK2)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1 in 16
  have eq50 (X1 : G) : ((sK1 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (X1 ◇ sK2)) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).1 in 36
  have eq77 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq95 (X0 X1 : G) : ((sK1 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (sK2 ◇ (X1 ◇ X0))) := superpose eq9 eq50 -- superposition 50,9, 9 into 50, unify on (0).2 in 9 and (0).2.2 in 50
  subsumption eq95 eq77


@[equational_result]
theorem Equation4540_implies_Equation4506 (G : Type*) [Magma G] (h : Equation4540 G) : Equation4506 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X3) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq36 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK2)) ≠ (sK0 ◇ (X1 ◇ sK0)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1 in 16
  have eq50 (X1 : G) : ((sK2 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (X1 ◇ sK0)) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).1 in 36
  have eq77 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq95 (X0 X1 : G) : ((sK2 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (X1 ◇ X0))) := superpose eq9 eq50 -- superposition 50,9, 9 into 50, unify on (0).2 in 9 and (0).2.2 in 50
  subsumption eq95 eq77


@[equational_result]
theorem Equation4540_implies_Equation4557 (G : Type*) [Magma G] (h : Equation4540 G) : Equation4557 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X3) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK3)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq36 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK2)) ≠ (sK0 ◇ (X1 ◇ sK3)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1 in 16
  have eq50 (X1 : G) : ((sK2 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (X1 ◇ sK3)) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).1 in 36
  have eq77 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq95 (X0 X1 : G) : ((sK2 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (sK3 ◇ (X1 ◇ X0))) := superpose eq9 eq50 -- superposition 50,9, 9 into 50, unify on (0).2 in 9 and (0).2.2 in 50
  subsumption eq95 eq77


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
theorem Equation454_implies_Equation446 (G : Type*) [Magma G] (h : Equation454 G) : Equation446 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2.2 in 9
  have eq27 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq35 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq27 eq27 -- superposition 27,27, 27 into 27, unify on (0).2 in 27 and (0).1.2.2 in 27
  have eq149 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X3 := superpose eq35 eq16 -- superposition 16,35, 35 into 16, unify on (0).2 in 35 and (0).1.2 in 16
  have eq263 : sK0 ≠ sK0 := superpose eq149 eq10 -- superposition 10,149, 149 into 10, unify on (0).2 in 149 and (0).2 in 10
  subsumption eq263 rfl


@[equational_result]
theorem Equation4545_implies_Equation4430 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4430 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK3 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq35 (X0 X1 : G) : (X1 ◇ (sK3 ◇ sK2)) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq47 (X1 : G) : ((sK2 ◇ sK3) ◇ sK3) ≠ (X1 ◇ (sK0 ◇ sK1)) := superpose eq9 eq35 -- superposition 35,9, 9 into 35, unify on (0).2 in 9 and (0).1 in 35
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq217 (X0 X1 X2 : G) : ((sK2 ◇ sK3) ◇ sK3) ≠ (X2 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  subsumption eq217 eq75


@[equational_result]
theorem Equation4545_implies_Equation4504 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4504 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK3 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq35 (X0 X1 : G) : (X1 ◇ (sK3 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq47 (X1 : G) : ((sK2 ◇ sK3) ◇ sK3) ≠ (X1 ◇ (sK1 ◇ sK1)) := superpose eq9 eq35 -- superposition 35,9, 9 into 35, unify on (0).2 in 9 and (0).1 in 35
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq217 (X0 X1 X2 : G) : ((sK2 ◇ sK3) ◇ sK3) ≠ (X2 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  subsumption eq217 eq75


@[equational_result]
theorem Equation4545_implies_Equation4521 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4521 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK3) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK3 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq35 (X0 X1 : G) : (X1 ◇ (sK3 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq47 (X1 : G) : ((sK0 ◇ sK3) ◇ sK3) ≠ (X1 ◇ (sK1 ◇ sK2)) := superpose eq9 eq35 -- superposition 35,9, 9 into 35, unify on (0).2 in 9 and (0).1 in 35
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq217 (X0 X1 X2 : G) : ((sK0 ◇ sK3) ◇ sK3) ≠ (X2 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  subsumption eq217 eq75


@[equational_result]
theorem Equation4545_implies_Equation4523 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4523 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq35 (X0 X1 : G) : (X1 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq51 (X1 : G) : ((sK2 ◇ sK1) ◇ sK1) ≠ (X1 ◇ (sK0 ◇ sK1)) := superpose eq9 eq35 -- superposition 35,9, 9 into 35, unify on (0).2 in 9 and (0).2 in 35
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq217 (X0 X1 X2 : G) : ((sK2 ◇ sK1) ◇ sK1) ≠ (X2 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq51 -- superposition 51,11, 11 into 51, unify on (0).2 in 11 and (0).2 in 51
  subsumption eq217 eq75


@[equational_result]
theorem Equation4545_implies_Equation4538 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4538 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK3) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK3 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq35 (X0 X1 : G) : (X1 ◇ (sK3 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq47 (X1 : G) : ((sK1 ◇ sK3) ◇ sK3) ≠ (X1 ◇ (sK1 ◇ sK2)) := superpose eq9 eq35 -- superposition 35,9, 9 into 35, unify on (0).2 in 9 and (0).1 in 35
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq217 (X0 X1 X2 : G) : ((sK1 ◇ sK3) ◇ sK3) ≠ (X2 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  subsumption eq217 eq75


@[equational_result]
theorem Equation4548_implies_Equation4527 (G : Type*) [Magma G] (h : Equation4548 G) : Equation4527 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X3) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq41 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK2)) ≠ (sK0 ◇ (X1 ◇ sK1)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq52 (X1 : G) : ((sK2 ◇ sK2) ◇ sK0) ≠ (sK0 ◇ (X1 ◇ sK1)) := superpose eq9 eq41 -- superposition 41,9, 9 into 41, unify on (0).2 in 9 and (0).1 in 41
  have eq81 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2 in 12
  have eq106 (X0 X1 X2 : G) : ((sK2 ◇ sK2) ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq52 -- superposition 52,12, 12 into 52, unify on (0).2 in 12 and (0).2.2 in 52
  subsumption eq106 eq81


@[equational_result]
theorem Equation4549_implies_Equation4576 (G : Type*) [Magma G] (h : Equation4549 G) : Equation4576 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK3) ◇ sK4) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (((X1 ◇ X1) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK4 ◇ sK3)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq40 (X0 X1 : G) : (X1 ◇ (sK4 ◇ sK3)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq51 (X1 : G) : ((sK3 ◇ sK3) ◇ sK4) ≠ (X1 ◇ (sK1 ◇ sK2)) := superpose eq9 eq40 -- superposition 40,9, 9 into 40, unify on (0).2 in 9 and (0).1 in 40
  have eq77 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ X0) = (X5 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).2.2 in 13
  have eq292 (X0 X1 X2 : G) : ((sK3 ◇ sK3) ◇ sK4) ≠ (X2 ◇ ((sK1 ◇ sK2) ◇ (X1 ◇ X0))) := superpose eq14 eq51 -- superposition 51,14, 14 into 51, unify on (0).2 in 14 and (0).2 in 51
  subsumption eq292 eq77


@[equational_result]
theorem Equation455_implies_Equation1053 (G : Type*) [Magma G] (h : Equation455 G) : Equation1053 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq32 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq32 rfl


@[equational_result]
theorem Equation4552_implies_Equation4567 (G : Type*) [Magma G] (h : Equation4552 G) : Equation4567 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 X3 X4 X5 : G) : ((X2 ◇ X5) ◇ X4) = (X4 ◇ (X2 ◇ (X3 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ X0)) = (((X2 ◇ X3) ◇ X0) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X0)) = (X2 ◇ (X4 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK3)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq82 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK3)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq210 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X5 ◇ X2)) = (X3 ◇ (X4 ◇ (X0 ◇ X1))) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq254 (X0 X2 X3 X4 : G) : (sK0 ◇ (sK3 ◇ (X0 ◇ (X2 ◇ X3)))) ≠ (sK0 ◇ (X4 ◇ sK2)) := superpose eq12 eq82 -- superposition 82,12, 12 into 82, unify on (0).2 in 12 and (0).1.2 in 82
  subsumption eq254 eq210


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
theorem Equation4560_implies_Equation4532 (G : Type*) [Magma G] (h : Equation4560 G) : Equation4532 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ X4)) = ((X5 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq17 (X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ X3)) = (X1 ◇ (X4 ◇ X5)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (X0 ◇ X1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq128 (X0 X3 X4 X5 X6 X7 : G) : (X3 ◇ (X6 ◇ X7)) = ((X0 ◇ (X4 ◇ X5)) ◇ X0) := superpose eq17 eq14 -- superposition 14,17, 17 into 14, unify on (0).2 in 17 and (0).2.1 in 14
  have eq156 (X2 X3 X4 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((X2 ◇ ((X3 ◇ X4) ◇ sK2)) ◇ X2) := superpose eq14 eq19 -- superposition 19,14, 14 into 19, unify on (0).2 in 14 and (0).2 in 19
  subsumption eq156 eq128


@[equational_result]
theorem Equation4562_implies_Equation4419 (G : Type*) [Magma G] (h : Equation4562 G) : Equation4419 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq16 (X1 X2 X3 X4 X5 : G) : (X4 ◇ (X2 ◇ X5)) = ((X2 ◇ (X1 ◇ X3)) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X2 ◇ (X1 ◇ X3)) = (X2 ◇ (X1 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ ((X2 ◇ X0) ◇ sK1)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.2 in 19
  have eq208 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X0 ◇ X5)) = (X3 ◇ ((X1 ◇ X2) ◇ X4)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq268 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2 in 20
  subsumption eq268 eq208


@[equational_result]
theorem Equation4562_implies_Equation4514 (G : Type*) [Magma G] (h : Equation4562 G) : Equation4514 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq16 (X1 X2 X3 X4 X5 : G) : (X4 ◇ (X2 ◇ X5)) = ((X2 ◇ (X1 ◇ X3)) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X2 ◇ (X1 ◇ X3)) = (X2 ◇ (X1 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ ((X2 ◇ X0) ◇ sK2)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.2 in 19
  have eq208 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X0 ◇ X5)) = (X3 ◇ ((X1 ◇ X2) ◇ X4)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq268 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2 in 20
  subsumption eq268 eq208


@[equational_result]
theorem Equation4562_implies_Equation4535 (G : Type*) [Magma G] (h : Equation4562 G) : Equation4535 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK3) ◇ sK0) := mod_symm nh
  have eq16 (X1 X2 X3 X4 X5 : G) : (X4 ◇ (X2 ◇ X5)) = ((X2 ◇ (X1 ◇ X3)) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X2 ◇ (X1 ◇ X3)) = (X2 ◇ (X1 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ ((X2 ◇ X0) ◇ sK3)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.2 in 19
  have eq208 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X0 ◇ X5)) = (X3 ◇ ((X1 ◇ X2) ◇ X4)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq268 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2 in 20
  subsumption eq268 eq208


@[equational_result]
theorem Equation4562_implies_Equation4548 (G : Type*) [Magma G] (h : Equation4562 G) : Equation4548 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq16 (X1 X2 X3 X4 X5 : G) : (X4 ◇ (X2 ◇ X5)) = ((X2 ◇ (X1 ◇ X3)) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X2 ◇ (X1 ◇ X3)) = (X2 ◇ (X1 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ ((X2 ◇ X0) ◇ sK2)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.2 in 19
  have eq208 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X0 ◇ X5)) = (X3 ◇ ((X1 ◇ X2) ◇ X4)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq268 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2 in 20
  subsumption eq268 eq208


@[equational_result]
theorem Equation456_implies_Equation57 (G : Type*) [Magma G] (h : Equation456 G) : Equation57 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 (X2 X3 : G) : (X2 ◇ X3) = X2 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq16 eq14


@[equational_result]
theorem Equation456_implies_Equation637 (G : Type*) [Magma G] (h : Equation456 G) : Equation637 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK2) ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 (X2 X3 : G) : (X2 ◇ X3) = X2 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq16 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq16 eq14


@[equational_result]
theorem Equation4567_implies_Equation4562 (G : Type*) [Magma G] (h : Equation4567 G) : Equation4562 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 X3 X4 X5 : G) : ((X5 ◇ X2) ◇ X4) = (X4 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ X2)) = ((X2 ◇ (X3 ◇ X1)) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X1)) = (X2 ◇ (X4 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq82 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq210 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X5 ◇ X0)) = (X3 ◇ (X4 ◇ (X1 ◇ X2))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq254 (X1 X2 X3 X4 : G) : (sK0 ◇ (sK1 ◇ (X1 ◇ (X2 ◇ X3)))) ≠ (sK0 ◇ (X4 ◇ sK2)) := superpose eq12 eq82 -- superposition 82,12, 12 into 82, unify on (0).2 in 12 and (0).1.2 in 82
  subsumption eq254 eq210


@[equational_result]
theorem Equation4568_implies_Equation4526 (G : Type*) [Magma G] (h : Equation4568 G) : Equation4526 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK0) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X1 ◇ X2)) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X1)) = (X4 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK3 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq77 (X0 X1 : G) : (X1 ◇ (sK3 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq293 (X1 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ (X3 ◇ X4)) = (X6 ◇ ((X7 ◇ X2) ◇ X1)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1 in 11
  have eq355 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ X2) ◇ X1)) ≠ (X5 ◇ (sK3 ◇ sK0)) := superpose eq11 eq77 -- superposition 77,11, 11 into 77, unify on (0).2 in 11 and (0).2 in 77
  subsumption eq355 eq293


@[equational_result]
theorem Equation4568_implies_Equation4567 (G : Type*) [Magma G] (h : Equation4568 G) : Equation4567 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X1 ◇ X2)) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X1)) = (X4 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq77 (X0 X1 : G) : (X1 ◇ (sK0 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq293 (X1 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ (X3 ◇ X4)) = (X6 ◇ ((X7 ◇ X2) ◇ X1)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1 in 11
  have eq355 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ X2) ◇ X1)) ≠ (X5 ◇ (sK1 ◇ sK2)) := superpose eq11 eq77 -- superposition 77,11, 11 into 77, unify on (0).2 in 11 and (0).1 in 77
  subsumption eq355 eq293


@[equational_result]
theorem Equation4568_implies_Equation4582 (G : Type*) [Magma G] (h : Equation4568 G) : Equation4582 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, sK5, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK4) ◇ sK5) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X1 ◇ X2)) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X1)) = (X4 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK5 ◇ sK4)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq77 (X0 X1 : G) : (X1 ◇ (sK5 ◇ sK4)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq293 (X1 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ (X3 ◇ X4)) = (X6 ◇ ((X7 ◇ X2) ◇ X1)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1 in 11
  have eq355 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ X2) ◇ X1)) ≠ (X5 ◇ (sK5 ◇ sK4)) := superpose eq11 eq77 -- superposition 77,11, 11 into 77, unify on (0).2 in 11 and (0).2 in 77
  subsumption eq355 eq293


@[equational_result]
theorem Equation457_implies_Equation644 (G : Type*) [Magma G] (h : Equation457 G) : Equation644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK2))) := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X3 ◇ (X4 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq16 eq14


@[equational_result]
theorem Equation4614_implies_Equation4627 (G : Type*) [Magma G] (h : Equation4614 G) : Equation4627 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK3) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X0) = ((X3 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X3) = (((X2 ◇ X0) ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X3) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq34 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((X0 ◇ sK3) ◇ sK3) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  have eq73 (X0 X1 : G) : ((sK0 ◇ sK0) ◇ X0) ≠ ((X1 ◇ sK3) ◇ sK3) := superpose eq17 eq34 -- superposition 34,17, 17 into 34, unify on (0).2 in 17 and (0).1 in 34
  have eq305 (X1 X2 X3 X4 : G) : ((X2 ◇ X2) ◇ X3) = ((X4 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq14 eq11 -- superposition 11,14, 14 into 11, unify on (0).2 in 14 and (0).2 in 11
  have eq341 (X1 X2 : G) : ((sK0 ◇ sK0) ◇ X2) ≠ ((X1 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) := superpose eq11 eq73 -- superposition 73,11, 11 into 73, unify on (0).2 in 11 and (0).2 in 73
  subsumption eq341 eq305


@[equational_result]
theorem Equation461_implies_Equation460 (G : Type*) [Magma G] (h : Equation461 G) : Equation460 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X5)) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq14 eq9 -- backward demodulation 9,14
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq16 eq15


@[equational_result]
theorem Equation463_implies_Equation491 (G : Type*) [Magma G] (h : Equation463 G) : Equation491 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) = (X1 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq13 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq17 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) = (X1 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ X0)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq19 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ X0) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq20 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ X0) = (X1 ◇ X0) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq33 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq20 eq20 -- superposition 20,20, 20 into 20, unify on (0).2 in 20 and (0).1 in 20
  have eq71 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X2 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) := superpose eq33 eq11 -- superposition 11,33, 33 into 11, unify on (0).2 in 33 and (0).2.2 in 11
  have eq73 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := superpose eq33 eq10 -- superposition 10,33, 33 into 10, unify on (0).2 in 33 and (0).2.2 in 10
  have eq117 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq20 eq17 -- superposition 17,20, 20 into 17, unify on (0).2 in 20 and (0).2.2 in 17
  have eq161 : sK0 ≠ (((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ (((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ (sK2 ◇ (sK2 ◇ sK0)))) := superpose eq17 eq73 -- superposition 73,17, 17 into 73, unify on (0).2 in 17 and (0).2 in 73
  have eq167 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1)))) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1)))) ◇ (X0 ◇ X1))) := superpose eq117 eq117 -- superposition 117,117, 117 into 117, unify on (0).2 in 117 and (0).1.1.2.2 in 117
  have eq225 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1))) := superpose eq117 eq167 -- forward demodulation 167,117
  have eq226 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1))) := superpose eq71 eq225 -- forward demodulation 225,71
  have eq227 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1))) := superpose eq9 eq226 -- forward demodulation 226,9
  have eq228 : sK0 ≠ (((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0)))) := superpose eq227 eq161 -- backward demodulation 161,227
  have eq229 : sK0 ≠ (((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq71 eq228 -- forward demodulation 228,71
  subsumption eq229 eq9


@[equational_result]
theorem Equation464_implies_Equation1832 (G : Type*) [Magma G] (h : Equation464 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq15 rfl


@[equational_result]
theorem Equation464_implies_Equation23 (G : Type*) [Magma G] (h : Equation464 G) : Equation23 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq14 : sK0 ≠ sK0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq14 rfl


@[equational_result]
theorem Equation465_implies_Equation2921 (G : Type*) [Magma G] (h : Equation465 G) : Equation2921 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq15 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq16 : sK0 ≠ (sK0 ◇ sK2) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq17 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq14 eq15 -- forward demodulation 15,14
  subsumption eq16 eq17


@[equational_result]
theorem Equation468_implies_Equation2907 (G : Type*) [Magma G] (h : Equation468 G) : Equation2907 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X3 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK2) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq18 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X1)) = X3 := superpose eq17 eq11 -- backward demodulation 11,17
  have eq20 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq18 eq17 -- backward demodulation 17,18
  have eq21 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq20 eq18 -- backward demodulation 18,20
  have eq23 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK2) := superpose eq20 eq14 -- backward demodulation 14,20
  have eq24 : sK0 ≠ (sK1 ◇ sK2) := superpose eq20 eq23 -- forward demodulation 23,20
  have eq27 (X0 X1 : G) : X0 = X1 := superpose eq21 eq20 -- superposition 20,21, 21 into 20, unify on (0).2 in 21 and (0).1 in 20
  have eq29 : sK0 ≠ sK1 := superpose eq20 eq24 -- superposition 24,20, 20 into 24, unify on (0).2 in 20 and (0).2 in 24
  subsumption eq29 eq27


@[equational_result]
theorem Equation469_implies_Equation603 (G : Type*) [Magma G] (h : Equation469 G) : Equation603 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) = (X3 ◇ (((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq21 (X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) = (X3 ◇ X1) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq69 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq21 eq21 -- superposition 21,21, 21 into 21, unify on (0).2 in 21 and (0).1 in 21
  have eq170 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq69 eq9 -- superposition 9,69, 69 into 9, unify on (0).2 in 69 and (0).1.2 in 9
  have eq178 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (X0 ◇ sK0)))) := superpose eq69 eq10 -- superposition 10,69, 69 into 10, unify on (0).2 in 69 and (0).2.2.2.2 in 10
  have eq495 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (X0 ◇ sK0)))) := superpose eq12 eq178 -- superposition 178,12, 12 into 178, unify on (0).2 in 12 and (0).2.2.2 in 178
  subsumption eq495 eq170


@[equational_result]
theorem Equation470_implies_Equation3177 (G : Type*) [Magma G] (h : Equation470 G) : Equation3177 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK2) ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq17 (X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X1))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2.2 in 9
  have eq18 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X2)) := superpose eq13 eq18 -- forward demodulation 18,13
  have eq32 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ X0)) ◇ X1) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq39 (X0 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X2 ◇ X0)) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).1.1 in 13
  have eq41 (X0 X1 X3 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ X1) = X0 := superpose eq19 eq32 -- forward demodulation 32,19
  have eq42 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq39 eq17 -- backward demodulation 17,39
  have eq47 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq42 eq41 -- backward demodulation 41,42
  have eq51 (X0 X1 : G) : X0 = X1 := superpose eq16 eq47 -- superposition 47,16, 16 into 47, unify on (0).2 in 16 and (0).1 in 47
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq14 -- superposition 14,47, 47 into 14, unify on (0).2 in 47 and (0).2 in 14
  subsumption eq61 eq51


@[equational_result]
theorem Equation471_implies_Equation472 (G : Type*) [Magma G] (h : Equation471 G) : Equation472 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X2))) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X0 := superpose eq12 eq13 -- forward demodulation 13,12
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq19 (X0 X1 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2.2 in 10
  subsumption eq19 eq17


@[equational_result]
theorem Equation474_implies_Equation8 (G : Type*) [Magma G] (h : Equation474 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq16 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq13 -- forward demodulation 13,8
  have eq17 : sK0 ≠ sK0 := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2 in 9
  subsumption eq17 rfl


@[equational_result]
theorem Equation475_implies_Equation750 (G : Type*) [Magma G] (h : Equation475 G) : Equation750 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X3 ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq15 (X1 X2 : G) : X1 = X2 := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq17 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ ((X0 ◇ X0) ◇ sK2))) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2.2.1 in 10
  subsumption eq17 eq15


@[equational_result]
theorem Equation478_implies_Equation480 (G : Type*) [Magma G] (h : Equation478 G) : Equation480 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq22 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq26 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.2 in 11
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq22 eq26 -- forward demodulation 26,22
  have eq30 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq29 eq22 -- backward demodulation 22,29
  have eq34 : sK0 ≠ (sK1 ◇ sK0) := superpose eq29 eq14 -- backward demodulation 14,29
  subsumption eq34 eq30


@[equational_result]
theorem Equation479_implies_Equation603 (G : Type*) [Magma G] (h : Equation479 G) : Equation603 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = (X3 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq13 eq12 -- backward demodulation 12,13
  have eq15 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq35 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).1.2 in 9
  have eq39 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2 in 15
  have eq98 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2)))) = (X4 ◇ (((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ (X4 ◇ (X1 ◇ X2)))) := superpose eq14 eq11 -- superposition 11,14, 14 into 11, unify on (0).2 in 14 and (0).1.2.2 in 11
  have eq143 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2)))) = X2 := superpose eq35 eq98 -- forward demodulation 98,35
  have eq336 : sK0 ≠ sK0 := superpose eq143 eq39 -- superposition 39,143, 143 into 39, unify on (0).2 in 143 and (0).2 in 39
  subsumption eq336 rfl


@[equational_result]
theorem Equation480_implies_Equation3196 (G : Type*) [Magma G] (h : Equation480 G) : Equation3196 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK2) ◇ sK1) ◇ sK0) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK3) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X1 ◇ X1))) = X3 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq19 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq12 eq14 -- superposition 14,12, 12 into 14, unify on (0).2 in 12 and (0).2 in 14
  have eq29 (X0 : G) : sK0 ≠ ((X0 ◇ sK0) ◇ sK3) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).2.1 in 16
  have eq30 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X3 ◇ (X1 ◇ X1))) = X3 := superpose eq19 eq17 -- backward demodulation 17,19
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X1) = X3 := superpose eq19 eq30 -- forward demodulation 30,19
  subsumption eq29 eq34


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
theorem Equation482_implies_Equation488 (G : Type*) [Magma G] (h : Equation482 G) : Equation488 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X0 ◇ (X4 ◇ X1)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ (sK1 ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 (X1 X2 : G) : X1 = X2 := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq19 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).2 in 16
  subsumption eq19 eq17


@[equational_result]
theorem Equation483_implies_Equation469 (G : Type*) [Magma G] (h : Equation483 G) : Equation469 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq9


@[equational_result]
theorem Equation484_implies_Equation470 (G : Type*) [Magma G] (h : Equation484 G) : Equation470 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X3 ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq18 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X3 ◇ X1))) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq19 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq14 eq9 -- backward demodulation 9,14
  have eq20 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq17 eq18 -- backward demodulation 18,17
  have eq24 : sK0 ≠ (sK1 ◇ sK0) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq29 (X1 X2 : G) : X1 = X2 := superpose eq19 eq20 -- superposition 20,19, 19 into 20, unify on (0).2 in 19 and (0).1 in 20
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq24 -- superposition 24,29, 29 into 24, unify on (0).2 in 29 and (0).2 in 24
  subsumption eq39 eq29


@[equational_result]
theorem Equation487_implies_Equation463 (G : Type*) [Magma G] (h : Equation487 G) : Equation463 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq30 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq49 : sK0 ≠ sK0 := superpose eq30 eq10 -- superposition 10,30, 30 into 10, unify on (0).2 in 30 and (0).2 in 10
  subsumption eq49 rfl


@[equational_result]
theorem Equation488_implies_Equation2788 (G : Type*) [Magma G] (h : Equation488 G) : Equation2788 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq14 (X0 X1 : G) : X0 = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq19 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 : sK0 ≠ (sK1 ◇ sK1) := superpose eq12 eq19 -- forward demodulation 19,12
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq20 -- superposition 20,14, 14 into 20, unify on (0).2 in 14 and (0).2 in 20
  subsumption eq27 eq14


@[equational_result]
theorem Equation490_implies_Equation589 (G : Type*) [Magma G] (h : Equation490 G) : Equation589 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ X1))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq15 : sK0 ≠ (sK1 ◇ sK3) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq15 eq14


@[equational_result]
theorem Equation491_implies_Equation39 (G : Type*) [Magma G] (h : Equation491 G) : Equation39 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation491_implies_Equation545 (G : Type*) [Magma G] (h : Equation491 G) : Equation545 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq37 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.2 in 9
  have eq42 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).2 in 15
  subsumption eq42 eq37


@[equational_result]
theorem Equation491_implies_Equation571 (G : Type*) [Magma G] (h : Equation491 G) : Equation571 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X1))) = (X3 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq13 eq12 -- backward demodulation 12,13
  have eq42 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (X0 ◇ (X0 ◇ sK0)))) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2.2 in 10
  have eq181 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ (X0 ◇ (X0 ◇ sK0)))) := superpose eq11 eq42 -- superposition 42,11, 11 into 42, unify on (0).2 in 11 and (0).2.2 in 42
  subsumption eq181 eq9


@[equational_result]
theorem Equation493_implies_Equation2991 (G : Type*) [Magma G] (h : Equation493 G) : Equation2991 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK1)) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq17 (X0 X3 X4 : G) : (X3 ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq26 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq17 eq9 -- backward demodulation 9,17
  have eq27 : sK0 ≠ ((sK2 ◇ sK0) ◇ sK1) := superpose eq17 eq10 -- backward demodulation 10,17
  subsumption eq27 eq26


@[equational_result]
theorem Equation494_implies_Equation1282 (G : Type*) [Magma G] (h : Equation494 G) : Equation1282 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK0) ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X1))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq15 (X2 X3 : G) : X2 = X3 := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq17 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2.1 in 10
  subsumption eq17 eq15


@[equational_result]
theorem Equation496_implies_Equation2713 (G : Type*) [Magma G] (h : Equation496 G) : Equation2713 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ X1) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq17 (X1 X2 : G) : X1 = X2 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq14 -- superposition 14,17, 17 into 14, unify on (0).2 in 17 and (0).2 in 14
  subsumption eq27 eq17


@[equational_result]
theorem Equation498_implies_Equation1959 (G : Type*) [Magma G] (h : Equation498 G) : Equation1959 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ (X5 ◇ X0))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq15 (X2 X3 : G) : X2 = X3 := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq17 eq15


@[equational_result]
theorem Equation500_implies_Equation419 (G : Type*) [Magma G] (h : Equation500 G) : Equation419 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq12 eq9


@[equational_result]
theorem Equation500_implies_Equation528 (G : Type*) [Magma G] (h : Equation500 G) : Equation528 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq12 eq9


@[equational_result]
theorem Equation500_implies_Equation575 (G : Type*) [Magma G] (h : Equation500 G) : Equation575 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1 in 11
  have eq15 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.2 in 9
  have eq38 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK0)))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  have eq82 : sK0 ≠ sK0 := superpose eq15 eq38 -- superposition 38,15, 15 into 38, unify on (0).2 in 15 and (0).2 in 38
  subsumption eq82 rfl


@[equational_result]
theorem Equation50_implies_Equation3659 (G : Type*) [Magma G] (h : Equation50 G) : Equation3659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation506_implies_Equation495 (G : Type*) [Magma G] (h : Equation506 G) : Equation495 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = (X3 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq32 (X0 X2 X3 : G) : (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq55 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2 in 9
  have eq61 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = (X3 ◇ (X3 ◇ (X1 ◇ X1))) := superpose eq55 eq11 -- backward demodulation 11,55
  have eq62 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := superpose eq55 eq10 -- backward demodulation 10,55
  have eq66 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq55 eq55 -- superposition 55,55, 55 into 55, unify on (0).2 in 55 and (0).2 in 55
  have eq83 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) = (X4 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))))) := superpose eq9 eq61 -- superposition 61,9, 9 into 61, unify on (0).2 in 9 and (0).1.2.2 in 61
  have eq147 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) = (X4 ◇ (X4 ◇ X1)) := superpose eq17 eq83 -- forward demodulation 83,17
  have eq148 (X1 X3 X4 : G) : (X3 ◇ (X1 ◇ X1)) = (X4 ◇ (X4 ◇ X1)) := superpose eq55 eq147 -- forward demodulation 147,55
  have eq505 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X2)))) = X2 := superpose eq66 eq32 -- superposition 32,66, 66 into 32, unify on (0).2 in 66 and (0).1.2 in 32
  have eq648 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ (X0 ◇ (X0 ◇ sK0)))) := superpose eq148 eq62 -- superposition 62,148, 148 into 62, unify on (0).2 in 148 and (0).2.2.2 in 62
  subsumption eq648 eq505


@[equational_result]
theorem Equation507_implies_Equation890 (G : Type*) [Magma G] (h : Equation507 G) : Equation890 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq28 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq29 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq35 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq29 eq28 -- backward demodulation 28,29
  have eq51 : sK0 ≠ (sK1 ◇ sK0) := superpose eq29 eq10 -- backward demodulation 10,29
  have eq52 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq29 eq35 -- forward demodulation 35,29
  subsumption eq51 eq52


@[equational_result]
theorem Equation510_implies_Equation3862 (G : Type*) [Magma G] (h : Equation510 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.2 in 8
  have eq15 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.2.2 in 8
  have eq16 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq10 eq15 -- forward demodulation 15,10
  have eq19 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).1.1 in 11
  have eq32 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq19 eq13 -- backward demodulation 13,19
  have eq39 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq32 eq9 -- superposition 9,32, 32 into 9, unify on (0).2 in 32 and (0).2 in 9
  subsumption eq39 rfl


@[equational_result]
theorem Equation510_implies_Equation439 (G : Type*) [Magma G] (h : Equation510 G) : Equation439 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.2 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq16 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2.2 in 9
  have eq17 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq11 eq16 -- forward demodulation 16,11
  have eq19 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq17 eq14 -- superposition 14,17, 17 into 14, unify on (0).2 in 17 and (0).2.1 in 14
  have eq20 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.1 in 12
  have eq27 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq19 eq17 -- backward demodulation 17,19
  have eq30 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq20 eq27 -- backward demodulation 27,20
  have eq66 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq30 eq9 -- superposition 9,30, 30 into 9, unify on (0).2 in 30 and (0).1.2.2.2 in 9
  have eq73 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq66 eq10 -- backward demodulation 10,66
  subsumption eq73 eq9


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
theorem Equation520_implies_Equation487 (G : Type*) [Magma G] (h : Equation520 G) : Equation487 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X2 := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1 in 14
  have eq38 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := superpose eq14 eq13 -- superposition 13,14, 14 into 13, unify on (0).2 in 14 and (0).2.2 in 13
  subsumption eq38 eq21


@[equational_result]
theorem Equation521_implies_Equation2918 (G : Type*) [Magma G] (h : Equation521 G) : Equation2918 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq19 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2) ◇ sK3) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq24 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq40 (X0 : G) : sK0 ≠ (((X0 ◇ (sK0 ◇ sK1)) ◇ sK2) ◇ sK3) := superpose eq15 eq19 -- superposition 19,15, 15 into 19, unify on (0).2 in 15 and (0).2.1.1 in 19
  have eq61 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq87 (X0 X2 X3 : G) : (X3 ◇ (X0 ◇ (X2 ◇ X0))) = X2 := superpose eq61 eq24 -- backward demodulation 24,61
  have eq101 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK3) := superpose eq61 eq40 -- backward demodulation 40,61
  have eq143 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq61 eq87 -- forward demodulation 87,61
  have eq144 (X0 X2 X3 : G) : (X3 ◇ X0) = X2 := superpose eq61 eq143 -- forward demodulation 143,61
  subsumption eq101 eq144


@[equational_result]
theorem Equation52_implies_Equation359 (G : Type*) [Magma G] (h : Equation52 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq11 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq11 rfl


@[equational_result]
theorem Equation524_implies_Equation608 (G : Type*) [Magma G] (h : Equation524 G) : Equation608 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X3 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq25 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X2)) = (X0 ◇ (X0 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq67 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq16 eq25 -- forward demodulation 25,16
  have eq68 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK4 ◇ sK0)))) := superpose eq67 eq10 -- backward demodulation 10,67
  have eq69 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := superpose eq67 eq68 -- forward demodulation 68,67
  subsumption eq69 eq16


@[equational_result]
theorem Equation52_implies_Equation629 (G : Type*) [Magma G] (h : Equation52 G) : Equation629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq12 eq9


@[equational_result]
theorem Equation528_implies_Equation4307 (G : Type*) [Magma G] (h : Equation528 G) : Equation4307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X3 ◇ (X3 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq25 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (X0 ◇ sK1)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq25 eq12


@[equational_result]
theorem Equation53_implies_Equation1038 (G : Type*) [Magma G] (h : Equation53 G) : Equation1038 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation537_implies_Equation583 (G : Type*) [Magma G] (h : Equation537 G) : Equation583 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq9


@[equational_result]
theorem Equation538_implies_Equation2772 (G : Type*) [Magma G] (h : Equation538 G) : Equation2772 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X0 ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq18 (X0 X2 X3 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X2))) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq22 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq23 (X0 X2 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := superpose eq14 eq18 -- forward demodulation 18,14
  have eq24 (X0 X2 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ X2) = X0 := superpose eq14 eq23 -- forward demodulation 23,14
  have eq25 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq14 eq24 -- forward demodulation 24,14
  have eq26 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq14 eq25 -- forward demodulation 25,14
  have eq31 : sK0 ≠ (sK0 ◇ sK2) := superpose eq14 eq22 -- forward demodulation 22,14
  subsumption eq31 eq26


@[equational_result]
theorem Equation541_implies_Equation487 (G : Type*) [Magma G] (h : Equation541 G) : Equation487 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = (X0 ◇ (X3 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = (X0 ◇ (X3 ◇ (X2 ◇ X2))) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq14 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2.2 in 9
  have eq101 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.2 in 14
  subsumption eq101 eq16


@[equational_result]
theorem Equation545_implies_Equation458 (G : Type*) [Magma G] (h : Equation545 G) : Equation458 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq29 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq52 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq29 -- forward demodulation 29,11
  have eq53 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq52 -- forward demodulation 52,9
  have eq54 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq53 -- forward demodulation 53,9
  have eq80 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X1 := superpose eq54 eq9 -- superposition 9,54, 54 into 9, unify on (0).2 in 54 and (0).1.2.2.2 in 9
  have eq93 (X0 : G) : sK0 ≠ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := superpose eq54 eq13 -- superposition 13,54, 54 into 13, unify on (0).2 in 54 and (0).2 in 13
  subsumption eq93 eq80


@[equational_result]
theorem Equation545_implies_Equation510 (G : Type*) [Magma G] (h : Equation545 G) : Equation510 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq29 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq52 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq29 -- forward demodulation 29,11
  have eq53 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq52 -- forward demodulation 52,9
  have eq54 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq53 -- forward demodulation 53,9
  have eq80 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X1 := superpose eq54 eq9 -- superposition 9,54, 54 into 9, unify on (0).2 in 54 and (0).1.2.2.2 in 9
  have eq95 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq54 eq13 -- superposition 13,54, 54 into 13, unify on (0).2 in 54 and (0).2.2 in 13
  subsumption eq95 eq80


@[equational_result]
theorem Equation545_implies_Equation562 (G : Type*) [Magma G] (h : Equation545 G) : Equation562 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq9


@[equational_result]
theorem Equation545_implies_Equation575 (G : Type*) [Magma G] (h : Equation545 G) : Equation575 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq29 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq52 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq29 -- forward demodulation 29,11
  have eq53 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq52 -- forward demodulation 52,9
  have eq54 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq53 -- forward demodulation 53,9
  have eq80 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X1 := superpose eq54 eq9 -- superposition 9,54, 54 into 9, unify on (0).2 in 54 and (0).1.2.2.2 in 9
  have eq95 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := superpose eq54 eq13 -- superposition 13,54, 54 into 13, unify on (0).2 in 54 and (0).2 in 13
  subsumption eq95 eq80


@[equational_result]
theorem Equation545_implies_Equation608 (G : Type*) [Magma G] (h : Equation545 G) : Equation608 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK4 ◇ sK0)))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq29 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq52 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq29 -- forward demodulation 29,11
  have eq53 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq52 -- forward demodulation 52,9
  have eq54 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq53 -- forward demodulation 53,9
  have eq80 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X1 := superpose eq54 eq9 -- superposition 9,54, 54 into 9, unify on (0).2 in 54 and (0).1.2.2.2 in 9
  have eq93 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK0 ◇ (sK4 ◇ sK0)))) := superpose eq54 eq13 -- superposition 13,54, 54 into 13, unify on (0).2 in 54 and (0).2 in 13
  subsumption eq93 eq80


@[equational_result]
theorem Equation547_implies_Equation691 (G : Type*) [Magma G] (h : Equation547 G) : Equation691 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK2 ◇ sK1) ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq19 (X0 X1 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2.2 in 10
  subsumption eq19 eq17


@[equational_result]
theorem Equation55_implies_Equation359 (G : Type*) [Magma G] (h : Equation55 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq13 rfl


@[equational_result]
theorem Equation554_implies_Equation541 (G : Type*) [Magma G] (h : Equation554 G) : Equation541 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X2 := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1 in 14
  have eq38 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (X0 ◇ (sK0 ◇ sK0)))) := superpose eq14 eq13 -- superposition 13,14, 14 into 13, unify on (0).2 in 14 and (0).2.2.2 in 13
  subsumption eq38 eq21


@[equational_result]
theorem Equation555_implies_Equation874 (G : Type*) [Magma G] (h : Equation555 G) : Equation874 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq22 (X1 X2 : G) : X1 = X2 := superpose eq12 eq16 -- superposition 16,12, 12 into 16, unify on (0).2 in 12 and (0).1 in 16
  have eq29 (X0 : G) : sK0 ≠ (sK1 ◇ X0) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2 in 10
  subsumption eq29 eq22


@[equational_result]
theorem Equation55_implies_Equation614 (G : Type*) [Magma G] (h : Equation55 G) : Equation614 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq8


@[equational_result]
theorem Equation556_implies_Equation43 (G : Type*) [Magma G] (h : Equation556 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation55_implies_Equation817 (G : Type*) [Magma G] (h : Equation55 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.2.2 in 8
  have eq20 : sK0 ≠ sK0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq20 rfl


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
theorem Equation571_implies_Equation520 (G : Type*) [Magma G] (h : Equation571 G) : Equation520 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq82 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))) = X1 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2.2 in 9
  have eq91 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2 in 10
  subsumption eq91 eq82


@[equational_result]
theorem Equation573_implies_Equation1296 (G : Type*) [Magma G] (h : Equation573 G) : Equation1296 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK2) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.1 in 12
  have eq21 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2))) = X0 := superpose eq15 eq11 -- backward demodulation 11,15
  have eq37 (X3 X4 : G) : X3 = X4 := superpose eq21 eq21 -- superposition 21,21, 21 into 21, unify on (0).2 in 21 and (0).1 in 21
  have eq65 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq37 eq10 -- superposition 10,37, 37 into 10, unify on (0).2 in 37 and (0).2.2.1 in 10
  subsumption eq65 eq37


@[equational_result]
theorem Equation57_implies_Equation457 (G : Type*) [Magma G] (h : Equation57 G) : Equation457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := mod_symm nh
  have eq11 : sK0 ≠ (sK0 ◇ sK1) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq13 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).2 in 11
  subsumption eq16 rfl


@[equational_result]
theorem Equation575_implies_Equation500 (G : Type*) [Magma G] (h : Equation575 G) : Equation500 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X3 ◇ (X3 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq30 (X0 : G) : sK0 ≠ (sK0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq30 eq9


@[equational_result]
theorem Equation579_implies_Equation506 (G : Type*) [Magma G] (h : Equation579 G) : Equation506 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq21 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X1)))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2.2 in 9
  have eq29 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (X0 ◇ sK0)))) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.2.2.2 in 14
  subsumption eq29 eq21


@[equational_result]
theorem Equation593_implies_Equation598 (G : Type*) [Magma G] (h : Equation593 G) : Equation598 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = (X2 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq24 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ sK0)))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq14


@[equational_result]
theorem Equation615_implies_Equation47 (G : Type*) [Magma G] (h : Equation615 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq11 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq11 rfl


@[equational_result]
theorem Equation616_implies_Equation47 (G : Type*) [Magma G] (h : Equation616 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.1 in 8
  have eq11 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq11 rfl


@[equational_result]
theorem Equation618_implies_Equation415 (G : Type*) [Magma G] (h : Equation618 G) : Equation415 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation621_implies_Equation625 (G : Type*) [Magma G] (h : Equation621 G) : Equation625 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation624_implies_Equation50 (G : Type*) [Magma G] (h : Equation624 G) : Equation50 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation626_implies_Equation624 (G : Type*) [Magma G] (h : Equation626 G) : Equation624 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK2))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) = X3 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq33 (X0 X3 X4 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ X0) ◇ X4))) = X3 := superpose eq9 eq26 -- superposition 26,9, 9 into 26, unify on (0).2 in 9 and (0).1.2.2.1.1 in 26
  have eq73 : sK0 ≠ sK0 := superpose eq33 eq10 -- superposition 10,33, 33 into 10, unify on (0).2 in 33 and (0).2 in 10
  subsumption eq73 rfl


@[equational_result]
theorem Equation62_implies_Equation719 (G : Type*) [Magma G] (h : Equation62 G) : Equation719 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq17 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X1 ◇ X0) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq31 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).2.2 in 11
  have eq38 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq31 eq10 -- backward demodulation 10,31
  subsumption eq38 eq9


@[equational_result]
theorem Equation631_implies_Equation654 (G : Type*) [Magma G] (h : Equation631 G) : Equation654 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation63_implies_Equation1922 (G : Type*) [Magma G] (h : Equation63 G) : Equation1922 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation63_implies_Equation23 (G : Type*) [Magma G] (h : Equation63 G) : Equation23 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq13 rfl


@[equational_result]
theorem Equation635_implies_Equation852 (G : Type*) [Magma G] (h : Equation635 G) : Equation852 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation636_implies_Equation855 (G : Type*) [Magma G] (h : Equation636 G) : Equation855 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK3))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq34 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2 in 9
  have eq62 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq34 eq10 -- backward demodulation 10,34
  subsumption eq62 eq34


@[equational_result]
theorem Equation637_implies_Equation650 (G : Type*) [Magma G] (h : Equation637 G) : Equation650 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X0 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : sK0 ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq14 -- superposition 14,12, 12 into 14, unify on (0).2 in 12 and (0).2 in 14
  subsumption eq17 rfl


@[equational_result]
theorem Equation644_implies_Equation459 (G : Type*) [Magma G] (h : Equation644 G) : Equation459 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1)))) := mod_symm nh
  have eq13 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : sK0 ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq13


@[equational_result]
theorem Equation645_implies_Equation55 (G : Type*) [Magma G] (h : Equation645 G) : Equation55 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation645_implies_Equation822 (G : Type*) [Magma G] (h : Equation645 G) : Equation822 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) = ((X2 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = ((X2 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.2 in 9
  have eq40 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) = ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) ◇ (X2 ◇ (X2 ◇ (X2 ◇ X3)))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq41 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq100 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).1.2.2 in 9
  have eq492 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq11 eq41 -- superposition 41,11, 11 into 41, unify on (0).2 in 11 and (0).1 in 41
  have eq913 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2)))))) = X2 := superpose eq12 eq492 -- superposition 492,12, 12 into 492, unify on (0).2 in 12 and (0).1.2.2.2 in 492
  have eq914 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X1 := superpose eq18 eq492 -- superposition 492,18, 18 into 492, unify on (0).2 in 18 and (0).1.2.2.2 in 492
  have eq1000 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))))) := superpose eq100 eq40 -- superposition 40,100, 100 into 40, unify on (0).2 in 100 and (0).1.2.2 in 40
  have eq1107 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))))) = X0 := superpose eq11 eq1000 -- forward demodulation 1000,11
  have eq2090 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq913 eq1107 -- superposition 1107,913, 913 into 1107, unify on (0).2 in 913 and (0).1.2.2 in 1107
  have eq3740 (X0 X1 : G) : (X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))))) = X0 := superpose eq2090 eq914 -- superposition 914,2090, 2090 into 914, unify on (0).2 in 2090 and (0).1.2.2.2.2 in 914
  have eq3781 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq3740 -- forward demodulation 3740,11
  have eq4012 : sK0 ≠ sK0 := superpose eq3781 eq10 -- superposition 10,3781, 3781 into 10, unify on (0).2 in 3781 and (0).2 in 10
  subsumption eq4012 rfl


@[equational_result]
theorem Equation646_implies_Equation56 (G : Type*) [Magma G] (h : Equation646 G) : Equation56 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


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
theorem Equation650_implies_Equation448 (G : Type*) [Magma G] (h : Equation650 G) : Equation448 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X1) = (((X2 ◇ X0) ◇ X1) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1)))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.1.2.1 in 12
  have eq21 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) = ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ (X5 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X5))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq30 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4)) = ((X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4)) ◇ ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq31 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) = ((X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq33 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2 in 12
  have eq36 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ (X3 ◇ (X2 ◇ X3)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2.1 in 12
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X3)) = ((X3 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2.1.2 in 12
  have eq55 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.2.2 in 21
  have eq271 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X4) = ((X2 ◇ X4) ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X4 ◇ (X2 ◇ X4)))) := superpose eq11 eq36 -- superposition 36,11, 11 into 36, unify on (0).2 in 11 and (0).2.2.1.2 in 36
  have eq372 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((((X2 ◇ (X1 ◇ X2)) ◇ (X3 ◇ ((X4 ◇ X1) ◇ X3))) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose eq55 eq12 -- superposition 12,55, 55 into 12, unify on (0).2 in 55 and (0).1.2.1.2 in 12
  have eq1433 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)))) := superpose eq23 eq271 -- superposition 271,23, 23 into 271, unify on (0).2 in 23 and (0).2.2.1 in 271
  have eq1434 (X0 X1 X2 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) = ((X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq23 eq55 -- superposition 55,23, 23 into 55, unify on (0).2 in 23 and (0).2.2 in 55
  have eq1436 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ ((((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X3))) = X3 := superpose eq23 eq33 -- superposition 33,23, 23 into 33, unify on (0).2 in 23 and (0).1.2.1 in 33
  have eq1518 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq1434 eq1433 -- backward demodulation 1433,1434
  have eq1578 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))))) := superpose eq13 eq37 -- superposition 37,13, 13 into 37, unify on (0).2 in 13 and (0).2.2.1.2.1 in 37
  have eq1579 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4)) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)))))) := superpose eq36 eq37 -- superposition 37,36, 36 into 37, unify on (0).2 in 36 and (0).2.2.1.2.1 in 37
  have eq1693 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X3 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3))) := superpose eq11 eq1578 -- forward demodulation 1578,11
  have eq1695 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4))) := superpose eq11 eq1579 -- forward demodulation 1579,11
  have eq1874 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)))) := superpose eq31 eq1695 -- superposition 1695,31, 31 into 1695, unify on (0).2 in 31 and (0).2.2.2 in 1695
  have eq1878 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq1695 eq9 -- superposition 9,1695, 1695 into 9, unify on (0).2 in 1695 and (0).1.2.2 in 9
  have eq1883 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose eq1695 eq12 -- superposition 12,1695, 1695 into 12, unify on (0).2 in 1695 and (0).1.2.1.2 in 12
  have eq2683 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq1693 eq12 -- superposition 12,1693, 1693 into 12, unify on (0).2 in 1693 and (0).1.2.1.2 in 12
  have eq2688 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq31 eq1878 -- superposition 1878,31, 31 into 1878, unify on (0).2 in 31 and (0).2.2.1.2 in 1878
  have eq2760 (X0 X1 X2 : G) : (X2 ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq31 eq1883 -- superposition 1883,31, 31 into 1883, unify on (0).2 in 31 and (0).1.2.1.1.2 in 1883
  have eq2846 (X0 X1 X2 X3 : G) : (X3 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq11 eq1436 -- superposition 1436,11, 11 into 1436, unify on (0).2 in 11 and (0).1.2.1.2 in 1436
  have eq2902 (X0 X1 X5 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X5))) := superpose eq21 eq1518 -- superposition 1518,21, 21 into 1518, unify on (0).2 in 21 and (0).1 in 1518
  have eq3015 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq2902 eq2760 -- backward demodulation 2760,2902
  have eq3016 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq2902 eq2688 -- backward demodulation 2688,2902
  have eq3017 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq2902 eq1874 -- backward demodulation 1874,2902
  have eq3019 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2))) = X2 := superpose eq11 eq3015 -- forward demodulation 3015,11
  have eq3020 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq3016 -- forward demodulation 3016,11
  have eq3027 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq3017 eq2846 -- backward demodulation 2846,3017
  have eq3160 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq3020 eq3019 -- superposition 3019,3020, 3020 into 3019, unify on (0).2 in 3020 and (0).1.2 in 3019
  have eq3180 (X0 X2 : G) : (X2 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq3020 eq372 -- superposition 372,3020, 3020 into 372, unify on (0).2 in 3020 and (0).1.2.1.1 in 372
  have eq3226 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X3)) = ((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ ((X4 ◇ (X0 ◇ X4)) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq3020 eq30 -- superposition 30,3020, 3020 into 30, unify on (0).2 in 3020 and (0).1.2.1 in 30
  have eq3250 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X3))) = X3 := superpose eq3160 eq3027 -- backward demodulation 3027,3160
  have eq3252 (X0 X1 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X3)) = ((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ (X4 ◇ (X0 ◇ X4))) := superpose eq3017 eq3226 -- forward demodulation 3226,3017
  have eq3255 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq3252 eq2683 -- backward demodulation 2683,3252
  have eq3300 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X3 ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3250 eq55 -- superposition 55,3250, 3250 into 55, unify on (0).2 in 3250 and (0).2.2 in 55
  have eq3301 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X3)))) := superpose eq3250 eq271 -- superposition 271,3250, 3250 into 271, unify on (0).2 in 3250 and (0).2.2.1 in 271
  have eq3310 (X0 X2 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2))) = X2 := superpose eq3300 eq3180 -- backward demodulation 3180,3300
  have eq3312 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3300 eq3301 -- forward demodulation 3301,3300
  have eq3326 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq3312 eq3255 -- backward demodulation 3255,3312
  have eq3413 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X2))) = X2 := superpose eq3312 eq33 -- superposition 33,3312, 3312 into 33, unify on (0).2 in 3312 and (0).1.2.1 in 33
  have eq3457 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq3312 eq9 -- superposition 9,3312, 3312 into 9, unify on (0).2 in 3312 and (0).1.2 in 9
  have eq3534 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X2))) := superpose eq3312 eq21 -- superposition 21,3312, 3312 into 21, unify on (0).2 in 3312 and (0).1 in 21
  have eq3590 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) = X2 := superpose eq3312 eq3413 -- forward demodulation 3413,3312
  have eq3656 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq3312 eq3457 -- superposition 3457,3312, 3312 into 3457, unify on (0).2 in 3312 and (0).1.2 in 3457
  have eq3685 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X3))) = X0 := superpose eq3457 eq3312 -- superposition 3312,3457, 3457 into 3312, unify on (0).2 in 3457 and (0).1 in 3312
  have eq3867 (X0 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X0))) = X2 := superpose eq3656 eq3310 -- backward demodulation 3310,3656
  have eq4044 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X3))) := superpose eq3867 eq11 -- superposition 11,3867, 3867 into 11, unify on (0).2 in 3867 and (0).1.2.1 in 11
  have eq4123 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := superpose eq3867 eq3685 -- superposition 3685,3867, 3867 into 3685, unify on (0).2 in 3867 and (0).1.2.2 in 3685
  have eq4159 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ X3) := superpose eq4123 eq4044 -- backward demodulation 4044,4123
  have eq4714 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X1) ◇ X3)))) := superpose eq4159 eq3534 -- backward demodulation 3534,4159
  have eq5273 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X3))) = X0 := superpose eq4159 eq3326 -- backward demodulation 3326,4159
  have eq5819 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq5273 eq4714 -- backward demodulation 4714,5273
  have eq5851 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq5819 eq3590 -- backward demodulation 3590,5819
  have eq5870 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq3656 eq5851 -- forward demodulation 5851,3656
  have eq5878 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq5870 eq3685 -- backward demodulation 3685,5870
  have eq5892 : sK0 ≠ (sK0 ◇ sK1) := superpose eq5870 eq10 -- backward demodulation 10,5870
  subsumption eq5892 eq5878


@[equational_result]
theorem Equation650_implies_Equation53 (G : Type*) [Magma G] (h : Equation650 G) : Equation53 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq21 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) = ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ (X5 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X5))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq31 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) = ((X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq33 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2 in 12
  have eq36 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ (X3 ◇ (X2 ◇ X3)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2.1 in 12
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X3)) = ((X3 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2.1.2 in 12
  have eq55 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.2.2 in 21
  have eq271 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X4) = ((X2 ◇ X4) ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X4 ◇ (X2 ◇ X4)))) := superpose eq11 eq36 -- superposition 36,11, 11 into 36, unify on (0).2 in 11 and (0).2.2.1.2 in 36
  have eq1433 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)))) := superpose eq23 eq271 -- superposition 271,23, 23 into 271, unify on (0).2 in 23 and (0).2.2.1 in 271
  have eq1434 (X0 X1 X2 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) = ((X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq23 eq55 -- superposition 55,23, 23 into 55, unify on (0).2 in 23 and (0).2.2 in 55
  have eq1436 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ ((((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X3))) = X3 := superpose eq23 eq33 -- superposition 33,23, 23 into 33, unify on (0).2 in 23 and (0).1.2.1 in 33
  have eq1518 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq1434 eq1433 -- backward demodulation 1433,1434
  have eq1572 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4)) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)))))) := superpose eq36 eq37 -- superposition 37,36, 36 into 37, unify on (0).2 in 36 and (0).2.2.1.2.1 in 37
  have eq1688 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4))) := superpose eq11 eq1572 -- forward demodulation 1572,11
  have eq1867 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)))) := superpose eq31 eq1688 -- superposition 1688,31, 31 into 1688, unify on (0).2 in 31 and (0).2.2.2 in 1688
  have eq1871 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq1688 eq9 -- superposition 9,1688, 1688 into 9, unify on (0).2 in 1688 and (0).1.2.2 in 9
  have eq1876 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose eq1688 eq12 -- superposition 12,1688, 1688 into 12, unify on (0).2 in 1688 and (0).1.2.1.2 in 12
  have eq2680 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq31 eq1871 -- superposition 1871,31, 31 into 1871, unify on (0).2 in 31 and (0).2.2.1.2 in 1871
  have eq2752 (X0 X1 X2 : G) : (X2 ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq31 eq1876 -- superposition 1876,31, 31 into 1876, unify on (0).2 in 31 and (0).1.2.1.1.2 in 1876
  have eq2838 (X0 X1 X2 X3 : G) : (X3 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq11 eq1436 -- superposition 1436,11, 11 into 1436, unify on (0).2 in 11 and (0).1.2.1.2 in 1436
  have eq2894 (X0 X1 X5 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X5))) := superpose eq21 eq1518 -- superposition 1518,21, 21 into 1518, unify on (0).2 in 21 and (0).1 in 1518
  have eq3007 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq2894 eq2752 -- backward demodulation 2752,2894
  have eq3008 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq2894 eq2680 -- backward demodulation 2680,2894
  have eq3009 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq2894 eq1867 -- backward demodulation 1867,2894
  have eq3011 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2))) = X2 := superpose eq11 eq3007 -- forward demodulation 3007,11
  have eq3012 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq3008 -- forward demodulation 3008,11
  have eq3019 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq3009 eq2838 -- backward demodulation 2838,3009
  have eq3151 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq3012 eq3011 -- superposition 3011,3012, 3012 into 3011, unify on (0).2 in 3012 and (0).1.2 in 3011
  have eq3241 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X3))) = X3 := superpose eq3151 eq3019 -- backward demodulation 3019,3151
  have eq3291 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X3 ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3241 eq55 -- superposition 55,3241, 3241 into 55, unify on (0).2 in 3241 and (0).2.2 in 55
  have eq3292 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X3)))) := superpose eq3241 eq271 -- superposition 271,3241, 3241 into 271, unify on (0).2 in 3241 and (0).2.2.1 in 271
  have eq3303 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3291 eq3292 -- forward demodulation 3292,3291
  have eq3450 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq3303 eq9 -- superposition 9,3303, 3303 into 9, unify on (0).2 in 3303 and (0).1.2 in 9
  have eq3666 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X3))) = X0 := superpose eq3450 eq3303 -- superposition 3303,3450, 3450 into 3303, unify on (0).2 in 3450 and (0).1 in 3303
  have eq4215 : sK0 ≠ sK0 := superpose eq3666 eq10 -- superposition 10,3666, 3666 into 10, unify on (0).2 in 3666 and (0).2 in 10
  subsumption eq4215 rfl


