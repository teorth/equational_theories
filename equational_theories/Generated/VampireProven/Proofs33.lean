import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation1374_implies_Equation1983 (G : Type*) [Magma G] (h : Equation1374 G) : Equation1983 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq30 (X0 X2 X3 : G) : (X0 ◇ X3) = (((X2 ◇ X0) ◇ X2) ◇ X3) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1.2 in 12
  have eq33 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = ((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X3) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1 in 12
  have eq62 (X1 X2 X3 : G) : (X1 ◇ X3) = ((X2 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq30 eq33 -- forward demodulation 33,30
  have eq180 : sK0 ≠ (sK2 ◇ (sK2 ◇ sK0)) := superpose eq62 eq10 -- superposition 10,62, 62 into 10, unify on (0).2 in 62 and (0).2 in 10
  subsumption eq180 eq22


@[equational_result]
theorem Equation1374_implies_Equation4200 (G : Type*) [Magma G] (h : Equation1374 G) : Equation4200 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK0) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq15 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq22 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq23 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq91 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose eq22 eq15 -- superposition 15,22, 22 into 15, unify on (0).2 in 22 and (0).1.2 in 15
  have eq95 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK2) ◇ sK1) := superpose eq91 eq10 -- backward demodulation 10,91
  subsumption eq95 eq23


@[equational_result]
theorem Equation1374_implies_Equation1231 (G : Type*) [Magma G] (h : Equation1374 G) : Equation1231 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq22 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq27 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq24 eq10 -- backward demodulation 10,24
  subsumption eq27 eq22


@[equational_result]
theorem Equation1374_implies_Equation1340 (G : Type*) [Magma G] (h : Equation1374 G) : Equation1340 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK2) ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq22 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq27 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq24 eq10 -- backward demodulation 10,24
  subsumption eq27 eq22


@[equational_result]
theorem Equation1374_implies_Equation1684 (G : Type*) [Magma G] (h : Equation1374 G) : Equation1684 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq15 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq92 : sK0 ≠ sK0 := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq92 rfl


@[equational_result]
theorem Equation1374_implies_Equation3997 (G : Type*) [Magma G] (h : Equation1374 G) : Equation3997 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK0 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq30 (X0 X2 X3 : G) : (X0 ◇ X3) = (((X2 ◇ X0) ◇ X2) ◇ X3) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1.2 in 12
  have eq33 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = ((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X3) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1 in 12
  have eq62 (X1 X2 X3 : G) : (X1 ◇ X3) = ((X2 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq30 eq33 -- forward demodulation 33,30
  have eq181 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq62 eq10 -- superposition 10,62, 62 into 10, unify on (0).2 in 62 and (0).2 in 10
  subsumption eq181 rfl


@[equational_result]
theorem Equation1374_implies_Equation4158 (G : Type*) [Magma G] (h : Equation1374 G) : Equation4158 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq15 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq22 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq23 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq91 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose eq22 eq15 -- superposition 15,22, 22 into 15, unify on (0).2 in 22 and (0).1.2 in 15
  have eq95 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := superpose eq91 eq10 -- backward demodulation 10,91
  subsumption eq95 eq23


@[equational_result]
theorem Equation1374_implies_Equation4635 (G : Type*) [Magma G] (h : Equation1374 G) : Equation4635 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq15 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq22 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq91 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose eq22 eq15 -- superposition 15,22, 22 into 15, unify on (0).2 in 22 and (0).1.2 in 15
  have eq257 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq91 eq10 -- superposition 10,91, 91 into 10, unify on (0).2 in 91 and (0).2 in 10
  subsumption eq257 rfl


@[equational_result]
theorem Equation1374_implies_Equation1691 (G : Type*) [Magma G] (h : Equation1374 G) : Equation1691 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq22 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq87 : sK0 ≠ sK0 := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).2 in 10
  subsumption eq87 rfl


@[equational_result]
theorem Equation1374_implies_Equation4677 (G : Type*) [Magma G] (h : Equation1374 G) : Equation4677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK1 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq15 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq22 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq91 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose eq22 eq15 -- superposition 15,22, 22 into 15, unify on (0).2 in 22 and (0).1.2 in 15
  have eq247 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq91 eq10 -- superposition 10,91, 91 into 10, unify on (0).2 in 91 and (0).2 in 10
  subsumption eq247 rfl


@[equational_result]
theorem Equation1374_implies_Equation3353 (G : Type*) [Magma G] (h : Equation1374 G) : Equation3353 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq22 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq87 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).2 in 10
  subsumption eq87 rfl


@[equational_result]
theorem Equation1374_implies_Equation4083 (G : Type*) [Magma G] (h : Equation1374 G) : Equation4083 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq15 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq22 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq23 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq91 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose eq22 eq15 -- superposition 15,22, 22 into 15, unify on (0).2 in 22 and (0).1.2 in 15
  have eq95 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := superpose eq91 eq10 -- backward demodulation 10,91
  subsumption eq95 eq23


@[equational_result]
theorem Equation1374_implies_Equation3334 (G : Type*) [Magma G] (h : Equation1374 G) : Equation3334 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq22 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq26 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq22 eq10 -- backward demodulation 10,22
  subsumption eq26 rfl


@[equational_result]
theorem Equation2584_implies_Equation3176 (G : Type*) [Magma G] (h : Equation2584 G) : Equation3176 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK2) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation2584_implies_Equation3139 (G : Type*) [Magma G] (h : Equation2584 G) : Equation3139 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ X2) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq15 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq17 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq18 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq51 : sK0 ≠ sK0 := superpose eq15 eq18 -- superposition 18,15, 15 into 18, unify on (0).2 in 15 and (0).2 in 18
  subsumption eq51 rfl


@[equational_result]
theorem Equation2584_implies_Equation3253 (G : Type*) [Magma G] (h : Equation2584 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ X2) = X2 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq16 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq8 eq12 -- forward demodulation 12,8
  have eq17 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq16 eq9 -- backward demodulation 9,16
  have eq18 : sK0 ≠ (sK0 ◇ sK0) := superpose eq16 eq17 -- forward demodulation 17,16
  subsumption eq18 eq16


@[equational_result]
theorem Equation2584_implies_Equation228 (G : Type*) [Magma G] (h : Equation2584 G) : Equation228 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2584_implies_Equation3102 (G : Type*) [Magma G] (h : Equation2584 G) : Equation3102 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ X2) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq16 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq17 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq19 : sK0 ≠ (sK0 ◇ sK0) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq19 eq17


@[equational_result]
theorem Equation2584_implies_Equation1629 (G : Type*) [Magma G] (h : Equation2584 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ X2) = X2 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq16 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq8 eq12 -- forward demodulation 12,8
  have eq17 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq16 eq9 -- backward demodulation 9,16
  have eq18 : sK0 ≠ (sK0 ◇ sK0) := superpose eq16 eq17 -- forward demodulation 17,16
  subsumption eq18 eq16


@[equational_result]
theorem Equation4102_implies_Equation3677 (G : Type*) [Magma G] (h : Equation4102 G) : Equation3677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq14 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq21 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ X0) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq21 eq14


@[equational_result]
theorem Equation4102_implies_Equation4098 (G : Type*) [Magma G] (h : Equation4102 G) : Equation4098 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq13 (X1 X2 X3 : G) : (X3 ◇ X3) = (((X2 ◇ X2) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq14 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq20 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq53 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq53 eq20


@[equational_result]
theorem Equation4102_implies_Equation4341 (G : Type*) [Magma G] (h : Equation4102 G) : Equation4341 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq14 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq20 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq79 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2.2 in 10
  subsumption eq79 rfl


@[equational_result]
theorem Equation4102_implies_Equation3687 (G : Type*) [Magma G] (h : Equation4102 G) : Equation3687 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq13 (X1 X2 X3 : G) : (X3 ◇ X3) = (((X2 ◇ X2) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq14 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq20 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X2) = ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X0) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.1.1 in 9
  have eq27 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X0) := superpose eq13 eq23 -- forward demodulation 23,13
  have eq70 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (sK1 ◇ sK0)) := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2.1 in 10
  subsumption eq70 eq27


@[equational_result]
theorem Equation4102_implies_Equation40 (G : Type*) [Magma G] (h : Equation4102 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq14 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq20 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq70 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq70 eq20


@[equational_result]
theorem Equation4102_implies_Equation3662 (G : Type*) [Magma G] (h : Equation4102 G) : Equation3662 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq13 (X1 X2 X3 : G) : (X3 ◇ X3) = (((X2 ◇ X2) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq14 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq20 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X2) = ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X0) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.1.1 in 9
  have eq26 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X0) := superpose eq13 eq22 -- forward demodulation 22,13
  have eq79 (X0 : G) : (X0 ◇ X0) ≠ ((X0 ◇ X0) ◇ (sK1 ◇ sK1)) := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).1 in 10
  subsumption eq79 eq26


@[equational_result]
theorem Equation4102_implies_Equation4083 (G : Type*) [Magma G] (h : Equation4102 G) : Equation4083 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq14 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq37 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).2 in 16
  subsumption eq37 eq21


@[equational_result]
theorem Equation4102_implies_Equation4068 (G : Type*) [Magma G] (h : Equation4102 G) : Equation4068 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X1 X2 X3 : G) : (X3 ◇ X3) = (((X2 ◇ X2) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq14 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq20 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq53 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq53 eq20


@[equational_result]
theorem Equation4102_implies_Equation4074 (G : Type*) [Magma G] (h : Equation4102 G) : Equation4074 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq14 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq42 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).2 in 16
  subsumption eq42 eq21


@[equational_result]
theorem Equation4102_implies_Equation3685 (G : Type*) [Magma G] (h : Equation4102 G) : Equation3685 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq13 (X1 X2 X3 : G) : (X3 ◇ X3) = (((X2 ◇ X2) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq14 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq20 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X2) = ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X0) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.1.1 in 9
  have eq26 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X0) := superpose eq13 eq22 -- forward demodulation 22,13
  have eq79 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (sK0 ◇ sK1)) := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2.1 in 10
  subsumption eq79 eq26


@[equational_result]
theorem Equation4102_implies_Equation4077 (G : Type*) [Magma G] (h : Equation4102 G) : Equation4077 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq14 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq42 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).2 in 16
  subsumption eq42 eq21


@[equational_result]
theorem Equation4102_implies_Equation4086 (G : Type*) [Magma G] (h : Equation4102 G) : Equation4086 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK0) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq14 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq42 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).2 in 16
  subsumption eq42 eq21


@[equational_result]
theorem Equation4102_implies_Equation4106 (G : Type*) [Magma G] (h : Equation4102 G) : Equation4106 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq14 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq37 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).2 in 16
  subsumption eq37 eq21


@[equational_result]
theorem Equation4102_implies_Equation4110 (G : Type*) [Magma G] (h : Equation4102 G) : Equation4110 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq14 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq42 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).2 in 16
  subsumption eq42 eq21


@[equational_result]
theorem Equation4102_implies_Equation4114 (G : Type*) [Magma G] (h : Equation4102 G) : Equation4114 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK3) ◇ sK2) := mod_symm nh
  have eq14 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq42 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).2 in 16
  subsumption eq42 eq21


@[equational_result]
theorem Equation444_implies_Equation817 (G : Type*) [Magma G] (h : Equation444 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq12 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = X2 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq9 -- backward demodulation 9,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation444_implies_Equation842 (G : Type*) [Magma G] (h : Equation444 G) : Equation842 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation444_implies_Equation1028 (G : Type*) [Magma G] (h : Equation444 G) : Equation1028 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation444_implies_Equation3725 (G : Type*) [Magma G] (h : Equation444 G) : Equation3725 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation444_implies_Equation1036 (G : Type*) [Magma G] (h : Equation444 G) : Equation1036 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation444_implies_Equation3256 (G : Type*) [Magma G] (h : Equation444 G) : Equation3256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 rfl


@[equational_result]
theorem Equation444_implies_Equation3662 (G : Type*) [Magma G] (h : Equation444 G) : Equation3662 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation444_implies_Equation3870 (G : Type*) [Magma G] (h : Equation444 G) : Equation3870 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 rfl


@[equational_result]
theorem Equation444_implies_Equation3319 (G : Type*) [Magma G] (h : Equation444 G) : Equation3319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 rfl


@[equational_result]
theorem Equation444_implies_Equation1020 (G : Type*) [Magma G] (h : Equation444 G) : Equation1020 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq12 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = X2 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq9 -- backward demodulation 9,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation444_implies_Equation835 (G : Type*) [Magma G] (h : Equation444 G) : Equation835 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq16 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation444_implies_Equation1832 (G : Type*) [Magma G] (h : Equation444 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq12 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = X2 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq9 -- backward demodulation 9,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation444_implies_Equation846 (G : Type*) [Magma G] (h : Equation444 G) : Equation846 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation444_implies_Equation3943 (G : Type*) [Magma G] (h : Equation444 G) : Equation3943 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 rfl


@[equational_result]
theorem Equation444_implies_Equation1865 (G : Type*) [Magma G] (h : Equation444 G) : Equation1865 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation444_implies_Equation3315 (G : Type*) [Magma G] (h : Equation444 G) : Equation3315 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 rfl


@[equational_result]
theorem Equation444_implies_Equation1857 (G : Type*) [Magma G] (h : Equation444 G) : Equation1857 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation444_implies_Equation8 (G : Type*) [Magma G] (h : Equation444 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq12 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = X2 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq15 rfl


@[equational_result]
theorem Equation444_implies_Equation858 (G : Type*) [Magma G] (h : Equation444 G) : Equation858 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq16 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation4524_implies_Equation4647 (G : Type*) [Magma G] (h : Equation4524 G) : Equation4647 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK2 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X0) = (X3 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = (((X1 ◇ X0) ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq19 (X0 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK1 ◇ ((X0 ◇ sK2) ◇ X0)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2.2 in 17
  have eq84 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = (X3 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X1)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq85 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).2 in 11
  have eq108 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) := superpose eq85 eq84 -- backward demodulation 84,85
  have eq213 (X0 X1 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK1 ◇ ((X0 ◇ (sK2 ◇ X1)) ◇ (sK2 ◇ X0))) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.2.1 in 19
  have eq224 (X0 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK1 ◇ (((X0 ◇ sK2) ◇ X0) ◇ sK2)) := superpose eq13 eq213 -- forward demodulation 213,13
  subsumption eq224 eq108


@[equational_result]
theorem Equation4524_implies_Equation4491 (G : Type*) [Magma G] (h : Equation4524 G) : Equation4491 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X0) = (X3 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X3)) = ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = (((X1 ◇ X0) ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X3)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ ((X0 ◇ sK2) ◇ X0)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2.2 in 17
  have eq22 (X0 X1 X3 X4 : G) : (X3 ◇ ((X1 ◇ X0) ◇ X1)) = (X3 ◇ (X0 ◇ X4)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).1.2 in 15
  have eq72 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).2 in 11
  have eq122 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ X2) = ((X2 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq202 (X0 X1 X2 X4 : G) : (X4 ◇ (((X0 ◇ X2) ◇ X0) ◇ X2)) = ((X0 ◇ ((X0 ◇ X1) ◇ X4)) ◇ X0) := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).1.2 in 12
  have eq268 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ sK2))) ◇ X0)) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2.2 in 18
  have eq289 (X0 X1 X4 : G) : ((X0 ◇ X4) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X4)) ◇ X0) := superpose eq72 eq202 -- forward demodulation 202,72
  have eq336 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ sK2)) ◇ X0)) := superpose eq289 eq268 -- forward demodulation 268,289
  have eq383 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ X4)) = (X0 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ X3)) := superpose eq22 eq22 -- superposition 22,22, 22 into 22, unify on (0).2 in 22 and (0).1 in 22
  have eq798 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X3)) = (((X1 ◇ X0) ◇ X1) ◇ X0) := superpose eq72 eq12 -- superposition 12,72, 72 into 12, unify on (0).2 in 72 and (0).2.1 in 12
  have eq812 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X4)) = ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X5)) ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq72 eq14 -- superposition 14,72, 72 into 14, unify on (0).2 in 72 and (0).1.2.1 in 14
  have eq876 (X0 X2 X4 : G) : (((X0 ◇ X2) ◇ X0) ◇ X2) = (X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X4)) := superpose eq798 eq812 -- forward demodulation 812,798
  have eq877 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ X2) := superpose eq72 eq876 -- forward demodulation 876,72
  have eq882 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = ((X2 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq877 eq122 -- backward demodulation 122,877
  have eq1001 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ X4)) = (X0 ◇ ((X3 ◇ X1) ◇ X3)) := superpose eq882 eq383 -- backward demodulation 383,882
  have eq1019 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)) := superpose eq882 eq336 -- backward demodulation 336,882
  subsumption eq1019 eq1001


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
theorem Equation3062_implies_Equation3260 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3260 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3062_implies_Equation3258 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3062_implies_Equation3085 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3085 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK2) ◇ sK0) ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1 in 14
  have eq37 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK2) ◇ X0) ◇ sK0) := superpose eq14 eq13 -- superposition 13,14, 14 into 13, unify on (0).2 in 14 and (0).2.1 in 13
  subsumption eq37 eq21


@[equational_result]
theorem Equation3062_implies_Equation4283 (G : Type*) [Magma G] (h : Equation3062 G) : Equation4283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3062_implies_Equation4672 (G : Type*) [Magma G] (h : Equation3062 G) : Equation4672 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK1) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK0) ◇ sK3) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq14 : ((sK0 ◇ sK0) ◇ sK3) ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 : G) : ((sK0 ◇ X0) ◇ sK3) ≠ ((sK0 ◇ X0) ◇ sK2) := superpose eq12 eq14 -- superposition 14,12, 12 into 14, unify on (0).2 in 12 and (0).1.1 in 14
  subsumption eq21 eq15


@[equational_result]
theorem Equation3062_implies_Equation4358 (G : Type*) [Magma G] (h : Equation3062 G) : Equation4358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3062_implies_Equation3334 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3334 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3062_implies_Equation3093 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3093 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK2) ◇ sK2) ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1 in 14
  have eq37 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK2) ◇ sK2) ◇ X0) := superpose eq14 eq13 -- superposition 13,14, 14 into 13, unify on (0).2 in 14 and (0).2 in 13
  subsumption eq37 eq21


@[equational_result]
theorem Equation3062_implies_Equation3083 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3083 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK2) ◇ sK2) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1 in 14
  have eq38 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ X0) ◇ sK2) ◇ sK2) := superpose eq14 eq13 -- superposition 13,14, 14 into 13, unify on (0).2 in 14 and (0).2.1.1 in 13
  subsumption eq38 eq21


@[equational_result]
theorem Equation3062_implies_Equation3465 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3465 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation3062_implies_Equation3537 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3537 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3062_implies_Equation3324 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3324 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3062_implies_Equation4631 (G : Type*) [Magma G] (h : Equation3062 G) : Equation4631 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation3062_implies_Equation3309 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3062_implies_Equation3326 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3062_implies_Equation4598 (G : Type*) [Magma G] (h : Equation3062 G) : Equation4598 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq20 (X0 : G) : ((sK0 ◇ X0) ◇ sK1) ≠ ((sK0 ◇ X0) ◇ sK0) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).1.1 in 13
  subsumption eq20 eq14


@[equational_result]
theorem Equation3062_implies_Equation3463 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3463 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq19 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation3062_implies_Equation3462 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3462 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq19 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation3062_implies_Equation4286 (G : Type*) [Magma G] (h : Equation3062 G) : Equation4286 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3062_implies_Equation3529 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3529 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3062_implies_Equation4676 (G : Type*) [Magma G] (h : Equation3062 G) : Equation4676 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK3) ◇ sK4) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK0) ◇ sK4) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq14 : ((sK0 ◇ sK0) ◇ sK4) ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 : G) : ((sK0 ◇ X0) ◇ sK4) ≠ ((sK0 ◇ X0) ◇ sK2) := superpose eq12 eq14 -- superposition 14,12, 12 into 14, unify on (0).2 in 12 and (0).1.1 in 14
  subsumption eq21 eq15


@[equational_result]
theorem Equation3062_implies_Equation3264 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3264 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3062_implies_Equation3257 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3257 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3062_implies_Equation3468 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3468 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq21 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2 in 13
  subsumption eq21 rfl


@[equational_result]
theorem Equation3062_implies_Equation3338 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3338 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3062_implies_Equation3469 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3469 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq21 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2 in 13
  subsumption eq21 rfl


@[equational_result]
theorem Equation3062_implies_Equation4673 (G : Type*) [Magma G] (h : Equation3062 G) : Equation4673 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq14 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq12 eq13 -- backward demodulation 13,12
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 : G) : ((sK0 ◇ X0) ◇ sK1) ≠ ((sK0 ◇ X0) ◇ sK2) := superpose eq12 eq14 -- superposition 14,12, 12 into 14, unify on (0).2 in 12 and (0).1.1 in 14
  subsumption eq21 eq15


@[equational_result]
theorem Equation3062_implies_Equation4288 (G : Type*) [Magma G] (h : Equation3062 G) : Equation4288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3062_implies_Equation3467 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3467 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq21 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2 in 13
  subsumption eq21 rfl


@[equational_result]
theorem Equation3062_implies_Equation309 (G : Type*) [Magma G] (h : Equation3062 G) : Equation309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq19 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation3062_implies_Equation3308 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3062_implies_Equation3069 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3069 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1 in 14
  have eq37 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ X0) ◇ sK1) ◇ sK1) := superpose eq14 eq13 -- superposition 13,14, 14 into 13, unify on (0).2 in 14 and (0).2.1.1 in 13
  subsumption eq37 eq21


@[equational_result]
theorem Equation3062_implies_Equation3263 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3263 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3062_implies_Equation3534 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3534 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3062_implies_Equation4361 (G : Type*) [Magma G] (h : Equation3062 G) : Equation4361 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ sK4)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3062_implies_Equation3331 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3331 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3062_implies_Equation3089 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3089 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK2) ◇ sK1) ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1 in 14
  have eq37 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK2) ◇ sK1) ◇ X0) := superpose eq14 eq13 -- superposition 13,14, 14 into 13, unify on (0).2 in 14 and (0).2 in 13
  subsumption eq37 eq21


@[equational_result]
theorem Equation3062_implies_Equation3509 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3509 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3062_implies_Equation3101 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3101 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK3) ◇ sK4) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK2) ◇ sK3) ◇ sK4) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1 in 14
  have eq37 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ X0) ◇ sK3) ◇ sK4) := superpose eq14 eq13 -- superposition 13,14, 14 into 13, unify on (0).2 in 14 and (0).2.1.1 in 13
  subsumption eq37 eq21


@[equational_result]
theorem Equation3062_implies_Equation3255 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3062_implies_Equation4601 (G : Type*) [Magma G] (h : Equation3062 G) : Equation4601 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq20 (X0 : G) : ((sK0 ◇ X0) ◇ sK1) ≠ ((sK0 ◇ X0) ◇ sK0) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).1.1 in 13
  subsumption eq20 eq14


@[equational_result]
theorem Equation3062_implies_Equation3511 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3511 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq13 -- backward demodulation 13,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation3062_implies_Equation3316 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3911_implies_Equation4091 (G : Type*) [Magma G] (h : Equation3911 G) : Equation4091 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq15 (X1 X4 X5 : G) : (X5 ◇ X5) = ((X4 ◇ X4) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq52 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq52 eq15


@[equational_result]
theorem Equation3911_implies_Equation4069 (G : Type*) [Magma G] (h : Equation3911 G) : Equation4069 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq15 (X1 X4 X5 : G) : (X5 ◇ X5) = ((X4 ◇ X4) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq52 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK2) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq52 eq15


@[equational_result]
theorem Equation3911_implies_Equation3908 (G : Type*) [Magma G] (h : Equation3911 G) : Equation3908 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK3) := mod_symm nh
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((X3 ◇ (X1 ◇ X1)) ◇ X0) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.1.2 in 9
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ (X0 ◇ X0)) ◇ sK3) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1.2 in 10
  subsumption eq26 eq24


@[equational_result]
theorem Equation3911_implies_Equation4098 (G : Type*) [Magma G] (h : Equation3911 G) : Equation4098 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq15 (X1 X4 X5 : G) : (X5 ◇ X5) = ((X4 ◇ X4) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq52 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK2) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq52 eq15


@[equational_result]
theorem Equation3911_implies_Equation4066 (G : Type*) [Magma G] (h : Equation3911 G) : Equation4066 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq15 (X1 X4 X5 : G) : (X5 ◇ X5) = ((X4 ◇ X4) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq58 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq58 eq15


@[equational_result]
theorem Equation3911_implies_Equation360 (G : Type*) [Magma G] (h : Equation3911 G) : Equation360 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq15 (X1 X4 X5 : G) : (X5 ◇ X5) = ((X4 ◇ X4) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq23 (X0 : G) : (X0 ◇ X0) ≠ ((X0 ◇ X0) ◇ sK1) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).1 in 10
  subsumption eq23 eq15


@[equational_result]
theorem Equation3911_implies_Equation4608 (G : Type*) [Magma G] (h : Equation3911 G) : Equation4608 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X2) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq15 (X1 X4 X5 : G) : (X5 ◇ X5) = ((X4 ◇ X4) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq52 (X0 : G) : (X0 ◇ X0) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq52 eq15


@[equational_result]
theorem Equation3911_implies_Equation359 (G : Type*) [Magma G] (h : Equation3911 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X2) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq14 (X1 X4 X5 : G) : (X5 ◇ X5) = ((X4 ◇ X4) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1 in 8
  have eq15 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2 in 8
  have eq25 (X0 : G) : (X0 ◇ X0) ≠ ((X0 ◇ X0) ◇ sK0) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).1 in 9
  subsumption eq25 eq14


@[equational_result]
theorem Equation3911_implies_Equation4096 (G : Type*) [Magma G] (h : Equation3911 G) : Equation4096 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq15 (X1 X4 X5 : G) : (X5 ◇ X5) = ((X4 ◇ X4) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq52 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq52 eq15


@[equational_result]
theorem Equation3911_implies_Equation4093 (G : Type*) [Magma G] (h : Equation3911 G) : Equation4093 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq15 (X1 X4 X5 : G) : (X5 ◇ X5) = ((X4 ◇ X4) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq58 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq58 eq15


@[equational_result]
theorem Equation3911_implies_Equation4597 (G : Type*) [Magma G] (h : Equation3911 G) : Equation4597 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X2) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq15 (X1 X4 X5 : G) : (X5 ◇ X5) = ((X4 ◇ X4) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq52 (X0 : G) : (X0 ◇ X0) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq52 eq15


@[equational_result]
theorem Equation3911_implies_Equation3872 (G : Type*) [Magma G] (h : Equation3911 G) : Equation3872 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((X3 ◇ (X1 ◇ X1)) ◇ X0) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.1.2 in 9
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK0 ◇ (X0 ◇ X0)) ◇ sK2) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1.2 in 10
  subsumption eq26 eq24


@[equational_result]
theorem Equation425_implies_Equation622 (G : Type*) [Magma G] (h : Equation425 G) : Equation622 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X4 ◇ (X5 ◇ X0))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq11


@[equational_result]
theorem Equation425_implies_Equation2246 (G : Type*) [Magma G] (h : Equation425 G) : Equation2246 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X4 ◇ (X5 ◇ X0))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation425_implies_Equation23 (G : Type*) [Magma G] (h : Equation425 G) : Equation23 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq9 -- backward demodulation 9,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation425_implies_Equation1833 (G : Type*) [Magma G] (h : Equation425 G) : Equation1833 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X4 : G) : (X4 ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation425_implies_Equation618 (G : Type*) [Magma G] (h : Equation425 G) : Equation618 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2))) := mod_symm nh
  have eq12 (X0 X4 : G) : (X4 ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation425_implies_Equation2243 (G : Type*) [Magma G] (h : Equation425 G) : Equation2243 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X4 ◇ (X5 ◇ X0))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation425_implies_Equation2852 (G : Type*) [Magma G] (h : Equation425 G) : Equation2852 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X4 : G) : (X4 ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq14 -- backward demodulation 14,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation425_implies_Equation100 (G : Type*) [Magma G] (h : Equation425 G) : Equation100 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X4 : G) : (X4 ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq12


@[equational_result]
theorem Equation425_implies_Equation819 (G : Type*) [Magma G] (h : Equation425 G) : Equation819 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X4 ◇ (X5 ◇ X0))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq11


@[equational_result]
theorem Equation425_implies_Equation620 (G : Type*) [Magma G] (h : Equation425 G) : Equation620 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq12 (X0 X4 : G) : (X4 ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq23 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq23 rfl


@[equational_result]
theorem Equation425_implies_Equation1430 (G : Type*) [Magma G] (h : Equation425 G) : Equation1430 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X4 ◇ (X5 ◇ X0))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq11


@[equational_result]
theorem Equation425_implies_Equation2443 (G : Type*) [Magma G] (h : Equation425 G) : Equation2443 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X4 : G) : (X4 ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq14 -- forward demodulation 14,12
  subsumption eq15 eq13


@[equational_result]
theorem Equation425_implies_Equation1630 (G : Type*) [Magma G] (h : Equation425 G) : Equation1630 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X4 : G) : (X4 ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq12


@[equational_result]
theorem Equation425_implies_Equation619 (G : Type*) [Magma G] (h : Equation425 G) : Equation619 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X4 : G) : (X4 ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation425_implies_Equation623 (G : Type*) [Magma G] (h : Equation425 G) : Equation623 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X4 ◇ (X5 ◇ X0))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq11


@[equational_result]
theorem Equation425_implies_Equation3921 (G : Type*) [Magma G] (h : Equation425 G) : Equation3921 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X4 : G) : (X4 ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 rfl


@[equational_result]
theorem Equation425_implies_Equation3255 (G : Type*) [Magma G] (h : Equation425 G) : Equation3255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X4 ◇ (X5 ◇ X0))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation425_implies_Equation4282 (G : Type*) [Magma G] (h : Equation425 G) : Equation4282 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X4 : G) : (X4 ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation425_implies_Equation1023 (G : Type*) [Magma G] (h : Equation425 G) : Equation1023 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X4 : G) : (X4 ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation425_implies_Equation1429 (G : Type*) [Magma G] (h : Equation425 G) : Equation1429 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X4 ◇ (X5 ◇ X0))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq11


@[equational_result]
theorem Equation425_implies_Equation2249 (G : Type*) [Magma G] (h : Equation425 G) : Equation2249 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X4 ◇ (X5 ◇ X0))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation425_implies_Equation1021 (G : Type*) [Magma G] (h : Equation425 G) : Equation1021 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X4 : G) : (X4 ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation425_implies_Equation2646 (G : Type*) [Magma G] (h : Equation425 G) : Equation2646 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X4 : G) : (X4 ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq14 -- forward demodulation 14,12
  subsumption eq15 eq13


@[equational_result]
theorem Equation425_implies_Equation1839 (G : Type*) [Magma G] (h : Equation425 G) : Equation1839 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X4 : G) : (X4 ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation3506_implies_Equation3473 (G : Type*) [Magma G] (h : Equation3506 G) : Equation3473 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X3) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq27 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2.1 in 9
  have eq29 (X0 : G) : (X0 ◇ X0) ≠ (sK1 ◇ ((X0 ◇ X0) ◇ sK2)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).1 in 10
  subsumption eq29 eq27


@[equational_result]
theorem Equation3506_implies_Equation3262 (G : Type*) [Magma G] (h : Equation3506 G) : Equation3262 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X3) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq15 (X3 X4 X5 : G) : (X4 ◇ X4) = (X5 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq61 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq61 eq15


@[equational_result]
theorem Equation3506_implies_Equation3484 (G : Type*) [Magma G] (h : Equation3506 G) : Equation3484 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X3) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq15 (X3 X4 X5 : G) : (X4 ◇ X4) = (X5 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ ((X0 ◇ X0) ◇ sK0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2.1 in 10
  have eq54 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X3) = (X4 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0)) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).2.2.1 in 9
  have eq61 (X1 X2 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ sK0)) := superpose eq15 eq26 -- superposition 26,15, 15 into 26, unify on (0).2 in 15 and (0).2.2.1 in 26
  subsumption eq61 eq54


@[equational_result]
theorem Equation3506_implies_Equation3678 (G : Type*) [Magma G] (h : Equation3506 G) : Equation3678 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X3) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq15 (X3 X4 X5 : G) : (X4 ◇ X4) = (X5 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2 in 10
  subsumption eq26 eq15


@[equational_result]
theorem Equation1636_implies_Equation4286 (G : Type*) [Magma G] (h : Equation1636 G) : Equation4286 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X3) ◇ (X0 ◇ X3)) ◇ (((X1 ◇ X0) ◇ X2) ◇ X4)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq44 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).2.1 in 16
  have eq56 : (sK0 ◇ (sK2 ◇ sK0)) ≠ (sK0 ◇ sK0) := superpose eq44 eq10 -- backward demodulation 10,44
  have eq63 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2.1 in 15
  have eq387 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq16 eq63 -- superposition 63,16, 16 into 63, unify on (0).2 in 16 and (0).2.2 in 63
  have eq479 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq387 eq56 -- superposition 56,387, 387 into 56, unify on (0).2 in 387 and (0).1 in 56
  subsumption eq479 rfl


@[equational_result]
theorem Equation1636_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1636 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.2.1 in 8
  have eq33 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.1 in 11
  have eq38 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq33 eq9 -- backward demodulation 9,33
  subsumption eq38 eq13


@[equational_result]
theorem Equation1636_implies_Equation2240 (G : Type*) [Magma G] (h : Equation1636 G) : Equation2240 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq44 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).2.1 in 16
  have eq56 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq44 eq10 -- backward demodulation 10,44
  subsumption eq56 eq12


@[equational_result]
theorem Equation1636_implies_Equation1633 (G : Type*) [Magma G] (h : Equation1636 G) : Equation1633 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X3) ◇ (X0 ◇ X3)) ◇ (((X1 ◇ X0) ◇ X2) ◇ X4)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq21 (X0 X3 X4 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ X4) = ((((X3 ◇ (X0 ◇ X0)) ◇ X4) ◇ ((X3 ◇ (X0 ◇ X0)) ◇ X4)) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq74 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2.1 in 15
  have eq138 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq14 eq21 -- superposition 21,14, 14 into 21, unify on (0).2 in 14 and (0).1.1 in 21
  have eq341 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq16 eq74 -- superposition 74,16, 16 into 74, unify on (0).2 in 16 and (0).2.2 in 74
  have eq378 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := superpose eq14 eq341 -- superposition 341,14, 14 into 341, unify on (0).2 in 14 and (0).2.2 in 341
  have eq451 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq378 eq138 -- backward demodulation 138,378
  have eq551 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq451 eq9 -- superposition 9,451, 451 into 9, unify on (0).2 in 451 and (0).1.2.1 in 9
  have eq949 : sK0 ≠ sK0 := superpose eq551 eq10 -- superposition 10,551, 551 into 10, unify on (0).2 in 551 and (0).2 in 10
  subsumption eq949 rfl


@[equational_result]
theorem Equation1636_implies_Equation3461 (G : Type*) [Magma G] (h : Equation1636 G) : Equation3461 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X3) ◇ (X0 ◇ X3)) ◇ (((X1 ◇ X0) ◇ X2) ◇ X4)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq74 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).2.1 in 15
  have eq341 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq16 eq74 -- superposition 74,16, 16 into 74, unify on (0).2 in 16 and (0).2.2 in 74
  have eq395 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq341 eq10 -- superposition 10,341, 341 into 10, unify on (0).2 in 341 and (0).2 in 10
  subsumption eq395 rfl


@[equational_result]
theorem Equation1636_implies_Equation1632 (G : Type*) [Magma G] (h : Equation1636 G) : Equation1632 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X3) ◇ (X0 ◇ X3)) ◇ (((X1 ◇ X0) ◇ X2) ◇ X4)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq21 (X0 X3 X4 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ X4) = ((((X3 ◇ (X0 ◇ X0)) ◇ X4) ◇ ((X3 ◇ (X0 ◇ X0)) ◇ X4)) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq74 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2.1 in 15
  have eq138 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq14 eq21 -- superposition 21,14, 14 into 21, unify on (0).2 in 14 and (0).1.1 in 21
  have eq341 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq16 eq74 -- superposition 74,16, 16 into 74, unify on (0).2 in 16 and (0).2.2 in 74
  have eq378 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := superpose eq14 eq341 -- superposition 341,14, 14 into 341, unify on (0).2 in 14 and (0).2.2 in 341
  have eq451 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq378 eq138 -- backward demodulation 138,378
  have eq551 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq451 eq9 -- superposition 9,451, 451 into 9, unify on (0).2 in 451 and (0).1.2.1 in 9
  have eq949 : sK0 ≠ sK0 := superpose eq551 eq10 -- superposition 10,551, 551 into 10, unify on (0).2 in 551 and (0).2 in 10
  subsumption eq949 rfl


@[equational_result]
theorem Equation1636_implies_Equation3254 (G : Type*) [Magma G] (h : Equation1636 G) : Equation3254 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq34 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1.1 in 12
  have eq44 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).2.1 in 16
  have eq56 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq44 eq10 -- backward demodulation 10,44
  subsumption eq56 eq34


@[equational_result]
theorem Equation1636_implies_Equation2452 (G : Type*) [Magma G] (h : Equation1636 G) : Equation2452 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq35 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.1 in 9
  have eq268 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq16 eq35 -- superposition 35,16, 16 into 35, unify on (0).2 in 16 and (0).2.2.1 in 35
  have eq312 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq268 eq10 -- backward demodulation 10,268
  subsumption eq312 eq12


@[equational_result]
theorem Equation1636_implies_Equation3467 (G : Type*) [Magma G] (h : Equation1636 G) : Equation3467 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X3) ◇ (X0 ◇ X3)) ◇ (((X1 ◇ X0) ◇ X2) ◇ X4)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq74 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2.1 in 15
  have eq341 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq16 eq74 -- superposition 74,16, 16 into 74, unify on (0).2 in 16 and (0).2.2 in 74
  have eq427 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq341 eq10 -- superposition 10,341, 341 into 10, unify on (0).2 in 341 and (0).2 in 10
  subsumption eq427 rfl


@[equational_result]
theorem Equation1636_implies_Equation3458 (G : Type*) [Magma G] (h : Equation1636 G) : Equation3458 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X3) ◇ (X0 ◇ X3)) ◇ (((X1 ◇ X0) ◇ X2) ◇ X4)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq74 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2.1 in 15
  have eq341 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq16 eq74 -- superposition 74,16, 16 into 74, unify on (0).2 in 16 and (0).2.2 in 74
  have eq395 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq341 eq10 -- superposition 10,341, 341 into 10, unify on (0).2 in 341 and (0).2 in 10
  subsumption eq395 rfl


@[equational_result]
theorem Equation1636_implies_Equation2246 (G : Type*) [Magma G] (h : Equation1636 G) : Equation2246 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq44 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).2.1 in 16
  have eq56 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq44 eq10 -- backward demodulation 10,44
  subsumption eq56 eq12


@[equational_result]
theorem Equation1636_implies_Equation1847 (G : Type*) [Magma G] (h : Equation1636 G) : Equation1847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X3) ◇ (X0 ◇ X3)) ◇ (((X1 ◇ X0) ◇ X2) ◇ X4)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq74 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2.1 in 15
  have eq341 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq16 eq74 -- superposition 74,16, 16 into 74, unify on (0).2 in 16 and (0).2.2 in 74
  have eq377 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq341 eq10 -- backward demodulation 10,341
  subsumption eq377 eq14


@[equational_result]
theorem Equation1636_implies_Equation3256 (G : Type*) [Magma G] (h : Equation1636 G) : Equation3256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq44 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).2.1 in 16
  have eq130 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq44 eq10 -- superposition 10,44, 44 into 10, unify on (0).2 in 44 and (0).2 in 10
  subsumption eq130 rfl


@[equational_result]
theorem Equation1636_implies_Equation3257 (G : Type*) [Magma G] (h : Equation1636 G) : Equation3257 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq44 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).2.1 in 16
  have eq130 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq44 eq10 -- superposition 10,44, 44 into 10, unify on (0).2 in 44 and (0).2 in 10
  subsumption eq130 rfl


@[equational_result]
theorem Equation1636_implies_Equation2449 (G : Type*) [Magma G] (h : Equation1636 G) : Equation2449 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq33 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq268 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq16 eq33 -- superposition 33,16, 16 into 33, unify on (0).2 in 16 and (0).2.2.1 in 33
  have eq312 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq268 eq10 -- backward demodulation 10,268
  subsumption eq312 eq12


@[equational_result]
theorem Equation1636_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1636 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.2.1 in 8
  have eq30 : sK0 ≠ sK0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2 in 9
  subsumption eq30 rfl


@[equational_result]
theorem Equation1636_implies_Equation2466 (G : Type*) [Magma G] (h : Equation1636 G) : Equation2466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X3) ◇ (X0 ◇ X3)) ◇ (((X1 ◇ X0) ◇ X2) ◇ X4)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq74 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2.1 in 15
  have eq339 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq11 eq74 -- superposition 74,11, 11 into 74, unify on (0).2 in 11 and (0).2.2 in 74
  have eq377 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq339 eq10 -- backward demodulation 10,339
  subsumption eq377 eq12


@[equational_result]
theorem Equation1636_implies_Equation4127 (G : Type*) [Magma G] (h : Equation1636 G) : Equation4127 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X3) ◇ (X0 ◇ X3)) ◇ (((X1 ◇ X0) ◇ X2) ◇ X4)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq21 (X0 X3 X4 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ X4) = ((((X3 ◇ (X0 ◇ X0)) ◇ X4) ◇ ((X3 ◇ (X0 ◇ X0)) ◇ X4)) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq74 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2.1 in 15
  have eq138 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq14 eq21 -- superposition 21,14, 14 into 21, unify on (0).2 in 14 and (0).1.1 in 21
  have eq341 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq16 eq74 -- superposition 74,16, 16 into 74, unify on (0).2 in 16 and (0).2.2 in 74
  have eq378 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq14 eq341 -- superposition 341,14, 14 into 341, unify on (0).2 in 14 and (0).2.2 in 341
  have eq451 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq378 eq138 -- backward demodulation 138,378
  have eq551 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq451 eq10 -- superposition 10,451, 451 into 10, unify on (0).2 in 451 and (0).2 in 10
  subsumption eq551 rfl


@[equational_result]
theorem Equation1636_implies_Equation1838 (G : Type*) [Magma G] (h : Equation1636 G) : Equation1838 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq44 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).2.1 in 16
  have eq56 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := superpose eq44 eq10 -- backward demodulation 10,44
  subsumption eq56 eq14


@[equational_result]
theorem Equation1636_implies_Equation3460 (G : Type*) [Magma G] (h : Equation1636 G) : Equation3460 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq35 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.1 in 9
  have eq268 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq16 eq35 -- superposition 35,16, 16 into 35, unify on (0).2 in 16 and (0).2.2.1 in 35
  have eq643 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq268 eq10 -- superposition 10,268, 268 into 10, unify on (0).2 in 268 and (0).2 in 10
  subsumption eq643 rfl


@[equational_result]
theorem Equation1636_implies_Equation1848 (G : Type*) [Magma G] (h : Equation1636 G) : Equation1848 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X3) ◇ (X0 ◇ X3)) ◇ (((X1 ◇ X0) ◇ X2) ◇ X4)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq74 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2.1 in 15
  have eq341 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq16 eq74 -- superposition 74,16, 16 into 74, unify on (0).2 in 16 and (0).2.2 in 74
  have eq377 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := superpose eq341 eq10 -- backward demodulation 10,341
  subsumption eq377 eq14


@[equational_result]
theorem Equation1636_implies_Equation1837 (G : Type*) [Magma G] (h : Equation1636 G) : Equation1837 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq44 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).2.1 in 16
  have eq56 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq44 eq10 -- backward demodulation 10,44
  subsumption eq56 eq14


@[equational_result]
theorem Equation1636_implies_Equation1833 (G : Type*) [Magma G] (h : Equation1636 G) : Equation1833 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq34 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1.1 in 12
  have eq39 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := superpose eq34 eq10 -- backward demodulation 10,34
  subsumption eq39 eq14


@[equational_result]
theorem Equation1636_implies_Equation308 (G : Type*) [Magma G] (h : Equation1636 G) : Equation308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq44 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).2.1 in 16
  have eq116 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq44 eq10 -- superposition 10,44, 44 into 10, unify on (0).2 in 44 and (0).2 in 10
  subsumption eq116 rfl


@[equational_result]
theorem Equation1636_implies_Equation1839 (G : Type*) [Magma G] (h : Equation1636 G) : Equation1839 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq44 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).2.1 in 16
  have eq56 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := superpose eq44 eq10 -- backward demodulation 10,44
  subsumption eq56 eq14


@[equational_result]
theorem Equation1636_implies_Equation2249 (G : Type*) [Magma G] (h : Equation1636 G) : Equation2249 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq44 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).2.1 in 16
  have eq56 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq44 eq10 -- backward demodulation 10,44
  subsumption eq56 eq12


