import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation2859_implies_Equation262 (G : Type*) [Magma G] (h : Equation2859 G) : Equation262 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X1) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq38 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK0) ◇ sK2) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1.1 in 10
  subsumption eq38 eq21


@[equational_result]
theorem Equation2859_implies_Equation2043 (G : Type*) [Magma G] (h : Equation2859 G) : Equation2043 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X1) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq45 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ X0) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq45 eq20


@[equational_result]
theorem Equation2859_implies_Equation2860 (G : Type*) [Magma G] (h : Equation2859 G) : Equation2860 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq22 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X1) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq29 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = ((X0 ◇ X3) ◇ X1) := superpose eq22 eq11 -- backward demodulation 11,22
  have eq53 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK1) ◇ sK2) := superpose eq29 eq10 -- superposition 10,29, 29 into 10, unify on (0).2 in 29 and (0).2.1 in 10
  subsumption eq53 eq22


@[equational_result]
theorem Equation2859_implies_Equation3320 (G : Type*) [Magma G] (h : Equation2859 G) : Equation3320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq23 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq23 eq16


@[equational_result]
theorem Equation2859_implies_Equation3511 (G : Type*) [Magma G] (h : Equation2859 G) : Equation3511 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq23 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq23 eq16


@[equational_result]
theorem Equation2859_implies_Equation258 (G : Type*) [Magma G] (h : Equation2859 G) : Equation258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X1) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq38 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK1) ◇ sK1) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1.1 in 10
  subsumption eq38 eq21


@[equational_result]
theorem Equation2859_implies_Equation4672 (G : Type*) [Magma G] (h : Equation2859 G) : Equation4672 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK1) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq38 (X0 : G) : ((sK0 ◇ X0) ◇ sK2) ≠ ((sK0 ◇ X0) ◇ sK3) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).1.1 in 10
  subsumption eq38 eq16


@[equational_result]
theorem Equation2859_implies_Equation3265 (G : Type*) [Magma G] (h : Equation2859 G) : Equation3265 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq26 eq16


@[equational_result]
theorem Equation2859_implies_Equation2044 (G : Type*) [Magma G] (h : Equation2859 G) : Equation2044 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X1) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq45 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ X0) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq45 eq20


@[equational_result]
theorem Equation2859_implies_Equation2040 (G : Type*) [Magma G] (h : Equation2859 G) : Equation2040 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X1) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq40 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ X0) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq40 eq21


@[equational_result]
theorem Equation2859_implies_Equation2074 (G : Type*) [Magma G] (h : Equation2859 G) : Equation2074 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X1) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq45 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ X0) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq45 eq20


@[equational_result]
theorem Equation2859_implies_Equation2650 (G : Type*) [Magma G] (h : Equation2859 G) : Equation2650 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X1) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq43 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ X0) ◇ sK1) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1 in 10
  subsumption eq43 eq20


@[equational_result]
theorem Equation2859_implies_Equation3470 (G : Type*) [Magma G] (h : Equation2859 G) : Equation3470 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq26 eq16


@[equational_result]
theorem Equation2859_implies_Equation2659 (G : Type*) [Magma G] (h : Equation2859 G) : Equation2659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X1) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq38 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1.1 in 10
  subsumption eq38 eq21


@[equational_result]
theorem Equation2859_implies_Equation3515 (G : Type*) [Magma G] (h : Equation2859 G) : Equation3515 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq23 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq23 eq16


@[equational_result]
theorem Equation2859_implies_Equation4288 (G : Type*) [Magma G] (h : Equation2859 G) : Equation4288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq26 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq26 eq12


@[equational_result]
theorem Equation2049_implies_Equation2066 (G : Type*) [Magma G] (h : Equation2049 G) : Equation2066 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X0) = (X0 ◇ (X3 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X4 : G) : (X4 ◇ X4) = (X4 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq27 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK2 ◇ sK0)) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq27 eq9


@[equational_result]
theorem Equation2049_implies_Equation2681 (G : Type*) [Magma G] (h : Equation2049 G) : Equation2681 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X0) = (X0 ◇ (X3 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X4 X5 : G) : (((X4 ◇ X4) ◇ X5) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 (X0 X4 : G) : (X4 ◇ X4) = (X4 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq28 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK2) := superpose eq17 eq14 -- backward demodulation 14,17
  subsumption eq28 eq13


@[equational_result]
theorem Equation2071_implies_Equation3308 (G : Type*) [Magma G] (h : Equation2071 G) : Equation3308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq21 (X0 X1 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ X5) ◇ (X0 ◇ X1)) = (((X0 ◇ X3) ◇ X0) ◇ X4) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq45 (X0 X3 X4 : G) : (((X0 ◇ X3) ◇ X0) ◇ X4) = X0 := superpose eq9 eq21 -- forward demodulation 21,9
  have eq55 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = ((((X0 ◇ X3) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) := superpose eq12 eq45 -- superposition 45,12, 12 into 45, unify on (0).2 in 12 and (0).1.1.1 in 45
  have eq73 (X0 X1 X4 : G) : (X0 ◇ X1) = (X0 ◇ X4) := superpose eq13 eq55 -- forward demodulation 55,13
  have eq139 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq73 eq10 -- superposition 10,73, 73 into 10, unify on (0).2 in 73 and (0).2.2 in 10
  subsumption eq139 eq73


@[equational_result]
theorem Equation2071_implies_Equation2898 (G : Type*) [Magma G] (h : Equation2071 G) : Equation2898 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK3) ◇ sK4) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq21 (X0 X1 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ X5) ◇ (X0 ◇ X1)) = (((X0 ◇ X3) ◇ X0) ◇ X4) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq37 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK0) ◇ sK4) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  have eq46 (X0 X3 X4 : G) : (((X0 ◇ X3) ◇ X0) ◇ X4) = X0 := superpose eq9 eq21 -- forward demodulation 21,9
  subsumption eq37 eq46


@[equational_result]
theorem Equation2857_implies_Equation3260 (G : Type*) [Magma G] (h : Equation2857 G) : Equation3260 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X2) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) ◇ X2) = ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X3) ◇ X4) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq33 (X0 X1 X2 X4 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) ◇ X2) = (X0 ◇ X4) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq34 (X0 X2 X4 : G) : (X0 ◇ X2) = (X0 ◇ X4) := superpose eq9 eq33 -- forward demodulation 33,9
  have eq62 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ X0))) := superpose eq34 eq10 -- superposition 10,34, 34 into 10, unify on (0).2 in 34 and (0).2.2.2 in 10
  subsumption eq62 eq34


@[equational_result]
theorem Equation2857_implies_Equation2883 (G : Type*) [Magma G] (h : Equation2857 G) : Equation2883 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X2) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq31 (X0 : G) : sK0 ≠ (((sK0 ◇ (sK0 ◇ X0)) ◇ X0) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq31 eq9


@[equational_result]
theorem Equation2857_implies_Equation2071 (G : Type*) [Magma G] (h : Equation2857 G) : Equation2071 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X2) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) ◇ X2) = ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X3) ◇ X4) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq18 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ X4) ◇ X5) = (((X0 ◇ (X0 ◇ X3)) ◇ X3) ◇ X2) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq33 (X0 X1 X2 X4 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) ◇ X2) = (X0 ◇ X4) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq34 (X0 X2 X4 : G) : (X0 ◇ X2) = (X0 ◇ X4) := superpose eq9 eq33 -- forward demodulation 33,9
  have eq36 (X0 X1 X4 X5 : G) : (((X0 ◇ X1) ◇ X4) ◇ X5) = X0 := superpose eq9 eq18 -- forward demodulation 18,9
  have eq57 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ X0) := superpose eq34 eq10 -- superposition 10,34, 34 into 10, unify on (0).2 in 34 and (0).2 in 10
  subsumption eq57 eq36


@[equational_result]
theorem Equation2857_implies_Equation2076 (G : Type*) [Magma G] (h : Equation2857 G) : Equation2076 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X2) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) ◇ X2) = ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X3) ◇ X4) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq18 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ X4) ◇ X5) = (((X0 ◇ (X0 ◇ X3)) ◇ X3) ◇ X2) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq33 (X0 X1 X2 X4 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) ◇ X2) = (X0 ◇ X4) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq34 (X0 X2 X4 : G) : (X0 ◇ X2) = (X0 ◇ X4) := superpose eq9 eq33 -- forward demodulation 33,9
  have eq36 (X0 X1 X4 X5 : G) : (((X0 ◇ X1) ◇ X4) ◇ X5) = X0 := superpose eq9 eq18 -- forward demodulation 18,9
  have eq62 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ X0) := superpose eq34 eq10 -- superposition 10,34, 34 into 10, unify on (0).2 in 34 and (0).2 in 10
  subsumption eq62 eq36


@[equational_result]
theorem Equation2864_implies_Equation2653 (G : Type*) [Magma G] (h : Equation2864 G) : Equation2653 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X2) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq61 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).1.1 in 11
  have eq65 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ X0) ◇ sK1) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1 in 10
  subsumption eq65 eq61


@[equational_result]
theorem Equation2864_implies_Equation2857 (G : Type*) [Magma G] (h : Equation2864 G) : Equation2857 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X2) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq57 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).1.1 in 11
  have eq61 (X0 : G) : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ sK2) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1 in 10
  subsumption eq61 eq57


@[equational_result]
theorem Equation2864_implies_Equation3468 (G : Type*) [Magma G] (h : Equation2864 G) : Equation3468 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X2) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq59 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2 in 10
  subsumption eq59 eq16


@[equational_result]
theorem Equation2864_implies_Equation2861 (G : Type*) [Magma G] (h : Equation2864 G) : Equation2861 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X2) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq57 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).1.1 in 11
  have eq61 (X0 : G) : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ sK3) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1 in 10
  subsumption eq61 eq57


@[equational_result]
theorem Equation2864_implies_Equation2856 (G : Type*) [Magma G] (h : Equation2864 G) : Equation2856 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X2) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq54 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK1) ◇ sK1) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1.1 in 10
  have eq133 (X0 : G) : sK0 ≠ (((sK0 ◇ (X0 ◇ sK0)) ◇ sK0) ◇ sK1) := superpose eq12 eq54 -- superposition 54,12, 12 into 54, unify on (0).2 in 12 and (0).2.1 in 54
  subsumption eq133 eq9


@[equational_result]
theorem Equation2864_implies_Equation3469 (G : Type*) [Magma G] (h : Equation2864 G) : Equation3469 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X2) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq62 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq62 eq16


@[equational_result]
theorem Equation2864_implies_Equation3259 (G : Type*) [Magma G] (h : Equation2864 G) : Equation3259 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X2) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq65 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ X0))) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2.2 in 10
  subsumption eq65 eq16


@[equational_result]
theorem Equation2667_implies_Equation2061 (G : Type*) [Magma G] (h : Equation2667 G) : Equation2061 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ X2) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq25 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ X0) ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq25 eq24


@[equational_result]
theorem Equation2667_implies_Equation2864 (G : Type*) [Magma G] (h : Equation2667 G) : Equation2864 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ X2) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq24 (X0 : G) : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) ◇ sK2) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq24 eq23


@[equational_result]
theorem Equation2667_implies_Equation2682 (G : Type*) [Magma G] (h : Equation2667 G) : Equation2682 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ X2) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq24 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq23


@[equational_result]
theorem Equation2667_implies_Equation2671 (G : Type*) [Magma G] (h : Equation2667 G) : Equation2671 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ X2) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq24 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq23


@[equational_result]
theorem Equation2667_implies_Equation326 (G : Type*) [Magma G] (h : Equation2667 G) : Equation326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation2667_implies_Equation2041 (G : Type*) [Magma G] (h : Equation2667 G) : Equation2041 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = (((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ X0) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq21 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ X0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq14 eq12 -- backward demodulation 12,14
  have eq38 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ X2) ◇ X3) = X0 := superpose eq36 eq14 -- backward demodulation 14,36
  subsumption eq21 eq38


@[equational_result]
theorem Equation262_implies_Equation4676 (G : Type*) [Magma G] (h : Equation262 G) : Equation4676 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK3) ◇ sK4) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq22 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK3) ◇ X0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  have eq54 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X4) ◇ X5) := superpose eq20 eq20 -- superposition 20,20, 20 into 20, unify on (0).2 in 20 and (0).1.1.1 in 20
  have eq76 (X0 X1 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ X0) ◇ X1) := superpose eq12 eq22 -- superposition 22,12, 12 into 22, unify on (0).2 in 12 and (0).2.1 in 22
  subsumption eq76 eq54


@[equational_result]
theorem Equation262_implies_Equation2667 (G : Type*) [Magma G] (h : Equation262 G) : Equation2667 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq22 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ X0) ◇ sK2) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq22 eq20


@[equational_result]
theorem Equation262_implies_Equation3541 (G : Type*) [Magma G] (h : Equation262 G) : Equation3541 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK3) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq22 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK3) ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq22 eq12


@[equational_result]
theorem Equation262_implies_Equation2669 (G : Type*) [Magma G] (h : Equation262 G) : Equation2669 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq22 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ X0) ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq22 eq20


@[equational_result]
theorem Equation1456_implies_Equation2270 (G : Type*) [Magma G] (h : Equation1456 G) : Equation2270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq49 : sK0 ≠ sK0 := superpose eq31 eq10 -- superposition 10,31, 31 into 10, unify on (0).2 in 31 and (0).2 in 10
  subsumption eq49 rfl


@[equational_result]
theorem Equation1456_implies_Equation2264 (G : Type*) [Magma G] (h : Equation1456 G) : Equation2264 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq49 : sK0 ≠ sK0 := superpose eq31 eq10 -- superposition 10,31, 31 into 10, unify on (0).2 in 31 and (0).2 in 10
  subsumption eq49 rfl


@[equational_result]
theorem Equation2270_implies_Equation1456 (G : Type*) [Magma G] (h : Equation2270 G) : Equation1456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 (X0 X1 X3 : G) : (X3 ◇ X0) = (X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq20 (X0 X1 X3 : G) : ((X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq25 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq18 eq20 -- forward demodulation 20,18
  have eq57 : sK0 ≠ sK0 := superpose eq25 eq10 -- superposition 10,25, 25 into 10, unify on (0).2 in 25 and (0).2 in 10
  subsumption eq57 rfl


@[equational_result]
theorem Equation2270_implies_Equation1454 (G : Type*) [Magma G] (h : Equation2270 G) : Equation1454 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 (X0 X1 X3 : G) : (X3 ◇ X0) = (X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq20 (X0 X1 X3 : G) : ((X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq25 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq18 eq20 -- forward demodulation 20,18
  have eq57 : sK0 ≠ sK0 := superpose eq25 eq10 -- superposition 10,25, 25 into 10, unify on (0).2 in 25 and (0).2 in 10
  subsumption eq57 rfl


@[equational_result]
theorem Equation2270_implies_Equation1427 (G : Type*) [Magma G] (h : Equation2270 G) : Equation1427 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 (X0 X1 X3 : G) : (X3 ◇ X0) = (X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq21 (X0 X1 X3 : G) : ((X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq26 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq18 eq21 -- forward demodulation 21,18
  have eq57 : sK0 ≠ sK0 := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq57 rfl


@[equational_result]
theorem Equation1879_implies_Equation1676 (G : Type*) [Magma G] (h : Equation1879 G) : Equation1676 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK3) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ X0) ◇ (X5 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1879_implies_Equation4134 (G : Type*) [Magma G] (h : Equation1879 G) : Equation4134 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ X0) ◇ (X5 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X3 X4 : G) : (X3 ◇ X0) = (((X3 ◇ X0) ◇ X4) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq73 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq73 rfl


@[equational_result]
theorem Equation1879_implies_Equation3326 (G : Type*) [Magma G] (h : Equation1879 G) : Equation3326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ X0) ◇ (X5 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq45 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq45 rfl


@[equational_result]
theorem Equation1879_implies_Equation159 (G : Type*) [Magma G] (h : Equation1879 G) : Equation159 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ X0) ◇ (X5 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1879_implies_Equation3258 (G : Type*) [Magma G] (h : Equation1879 G) : Equation3258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ X0) ◇ (X5 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq45 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq45 rfl


@[equational_result]
theorem Equation1879_implies_Equation1640 (G : Type*) [Magma G] (h : Equation1879 G) : Equation1640 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ X0) ◇ (X5 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1879_implies_Equation1644 (G : Type*) [Magma G] (h : Equation1879 G) : Equation1644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ X0) ◇ (X5 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1879_implies_Equation1650 (G : Type*) [Magma G] (h : Equation1879 G) : Equation1650 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ X0) ◇ (X5 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1879_implies_Equation1631 (G : Type*) [Magma G] (h : Equation1879 G) : Equation1631 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ X0) ◇ (X5 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1879_implies_Equation1637 (G : Type*) [Magma G] (h : Equation1879 G) : Equation1637 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ X0) ◇ (X5 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1879_implies_Equation1672 (G : Type*) [Magma G] (h : Equation1879 G) : Equation1672 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ X0) ◇ (X5 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1879_implies_Equation162 (G : Type*) [Magma G] (h : Equation1879 G) : Equation162 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ X0) ◇ (X5 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1676_implies_Equation1879 (G : Type*) [Magma G] (h : Equation1676 G) : Equation1879 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ (X0 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1676_implies_Equation1853 (G : Type*) [Magma G] (h : Equation1676 G) : Equation1853 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ (X0 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1676_implies_Equation4067 (G : Type*) [Magma G] (h : Equation1676 G) : Equation4067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ (X0 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 (X0 X2 X3 : G) : (X2 ◇ X0) = (((X2 ◇ X0) ◇ X3) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq76 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq76 rfl


@[equational_result]
theorem Equation1676_implies_Equation1857 (G : Type*) [Magma G] (h : Equation1676 G) : Equation1857 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ (X0 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1676_implies_Equation1867 (G : Type*) [Magma G] (h : Equation1676 G) : Equation1867 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ (X0 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1676_implies_Equation1863 (G : Type*) [Magma G] (h : Equation1676 G) : Equation1863 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ (X0 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1676_implies_Equation1843 (G : Type*) [Magma G] (h : Equation1676 G) : Equation1843 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ (X0 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3083_implies_Equation3094 (G : Type*) [Magma G] (h : Equation3083 G) : Equation3094 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq26 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X1) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq28 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK1) ◇ X0) ◇ X0) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq28 eq26


@[equational_result]
theorem Equation3053_implies_Equation3066 (G : Type*) [Magma G] (h : Equation3053 G) : Equation3066 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1 in 11
  have eq15 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.1 in 9
  have eq43 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK1) ◇ X0) ◇ X0) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  have eq82 : sK0 ≠ sK0 := superpose eq15 eq43 -- superposition 43,15, 15 into 43, unify on (0).2 in 15 and (0).2 in 43
  subsumption eq82 rfl


@[equational_result]
theorem Equation3053_implies_Equation3079 (G : Type*) [Magma G] (h : Equation3053 G) : Equation3079 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq12 eq9


@[equational_result]
theorem Equation3053_implies_Equation3083 (G : Type*) [Magma G] (h : Equation3053 G) : Equation3083 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK2) ◇ sK2) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq12 eq9


@[equational_result]
theorem Equation3094_implies_Equation4656 (G : Type*) [Magma G] (h : Equation3094 G) : Equation4656 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (((X0 ◇ X3) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X3) = ((((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X4) ◇ X4) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq27 (X0 X1 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X3) ◇ X3) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq42 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X3) ◇ X3) := superpose eq27 eq12 -- backward demodulation 12,27
  have eq90 (X0 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK0 ◇ X0) ◇ X0) := superpose eq42 eq10 -- superposition 10,42, 42 into 10, unify on (0).2 in 42 and (0).2 in 10
  subsumption eq90 eq42


@[equational_result]
theorem Equation3094_implies_Equation3075 (G : Type*) [Magma G] (h : Equation3094 G) : Equation3075 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (((X0 ◇ X3) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq34 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK1) ◇ X0) ◇ X0) ◇ sK1) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq34 eq9


@[equational_result]
theorem Equation3094_implies_Equation3053 (G : Type*) [Magma G] (h : Equation3094 G) : Equation3053 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (((X0 ◇ X3) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq34 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ X0) ◇ X0) ◇ sK0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq34 eq9


@[equational_result]
theorem Equation2485_implies_Equation1662 (G : Type*) [Magma G] (h : Equation2485 G) : Equation1662 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq69 : sK0 ≠ sK0 := superpose eq36 eq10 -- superposition 10,36, 36 into 10, unify on (0).2 in 36 and (0).2 in 10
  subsumption eq69 rfl


@[equational_result]
theorem Equation2485_implies_Equation1632 (G : Type*) [Magma G] (h : Equation2485 G) : Equation1632 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq40 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq69 : sK0 ≠ sK0 := superpose eq40 eq10 -- superposition 10,40, 40 into 10, unify on (0).2 in 40 and (0).2 in 10
  subsumption eq69 rfl


@[equational_result]
theorem Equation2485_implies_Equation1654 (G : Type*) [Magma G] (h : Equation2485 G) : Equation1654 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq69 : sK0 ≠ sK0 := superpose eq36 eq10 -- superposition 10,36, 36 into 10, unify on (0).2 in 36 and (0).2 in 10
  subsumption eq69 rfl


@[equational_result]
theorem Equation1662_implies_Equation2485 (G : Type*) [Magma G] (h : Equation1662 G) : Equation2485 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq76 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq76 rfl


@[equational_result]
theorem Equation1662_implies_Equation2457 (G : Type*) [Magma G] (h : Equation1662 G) : Equation2457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq76 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq76 rfl


@[equational_result]
theorem Equation1662_implies_Equation2449 (G : Type*) [Magma G] (h : Equation1662 G) : Equation2449 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq76 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq76 rfl


@[equational_result]
theorem Equation2481_implies_Equation1661 (G : Type*) [Magma G] (h : Equation2481 G) : Equation1661 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X1)) = (X0 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq35 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq35 eq12


@[equational_result]
theorem Equation2481_implies_Equation4127 (G : Type*) [Magma G] (h : Equation2481 G) : Equation4127 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2481_implies_Equation1655 (G : Type*) [Magma G] (h : Equation2481 G) : Equation1655 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X1)) = (X0 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq35 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq35 eq12


@[equational_result]
theorem Equation2481_implies_Equation3083 (G : Type*) [Magma G] (h : Equation2481 G) : Equation3083 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation2481_implies_Equation3525 (G : Type*) [Magma G] (h : Equation2481 G) : Equation3525 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) ≠ (sK0 ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X1)) = (X0 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq36 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).1 in 10
  subsumption eq36 rfl


@[equational_result]
theorem Equation2481_implies_Equation3518 (G : Type*) [Magma G] (h : Equation2481 G) : Equation3518 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 rfl


@[equational_result]
theorem Equation2481_implies_Equation1873 (G : Type*) [Magma G] (h : Equation2481 G) : Equation1873 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2481_implies_Equation3519 (G : Type*) [Magma G] (h : Equation2481 G) : Equation3519 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X1)) = (X0 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq36 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq36 rfl


@[equational_result]
theorem Equation2481_implies_Equation2485 (G : Type*) [Magma G] (h : Equation2481 G) : Equation2485 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation2481_implies_Equation1838 (G : Type*) [Magma G] (h : Equation2481 G) : Equation1838 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2481_implies_Equation4073 (G : Type*) [Magma G] (h : Equation2481 G) : Equation4073 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 rfl


@[equational_result]
theorem Equation2481_implies_Equation3458 (G : Type*) [Magma G] (h : Equation2481 G) : Equation3458 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X1)) = (X0 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq34 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq34 rfl


@[equational_result]
theorem Equation2481_implies_Equation4068 (G : Type*) [Magma G] (h : Equation2481 G) : Equation4068 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1661_implies_Equation2481 (G : Type*) [Magma G] (h : Equation1661 G) : Equation2481 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq35 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq22 eq18 -- backward demodulation 18,22
  have eq38 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq22 eq10 -- backward demodulation 10,22
  subsumption eq38 eq35


@[equational_result]
theorem Equation1661_implies_Equation4135 (G : Type*) [Magma G] (h : Equation1661 G) : Equation4135 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq22 eq18 -- backward demodulation 18,22
  have eq41 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq37 eq10 -- superposition 10,37, 37 into 10, unify on (0).2 in 37 and (0).2 in 10
  subsumption eq41 rfl


@[equational_result]
theorem Equation1661_implies_Equation4146 (G : Type*) [Magma G] (h : Equation1661 G) : Equation4146 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq22 eq18 -- backward demodulation 18,22
  have eq38 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq37 eq10 -- backward demodulation 10,37
  subsumption eq38 rfl


@[equational_result]
theorem Equation1661_implies_Equation4065 (G : Type*) [Magma G] (h : Equation1661 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq17 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X1 := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1.2 in 11
  have eq21 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).1.1 in 12
  have eq36 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq21 eq17 -- backward demodulation 17,21
  have eq37 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq36 eq9 -- backward demodulation 9,36
  subsumption eq37 rfl


@[equational_result]
theorem Equation1661_implies_Equation3459 (G : Type*) [Magma G] (h : Equation1661 G) : Equation3459 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq22 eq18 -- backward demodulation 18,22
  have eq38 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq37 eq10 -- backward demodulation 10,37
  subsumption eq38 rfl


@[equational_result]
theorem Equation1661_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1661 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq17 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X1 := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1.2 in 11
  have eq21 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).1.1 in 12
  have eq36 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq21 eq17 -- backward demodulation 17,21
  have eq39 : sK0 ≠ sK0 := superpose eq36 eq9 -- superposition 9,36, 36 into 9, unify on (0).2 in 36 and (0).2 in 9
  subsumption eq39 rfl


@[equational_result]
theorem Equation1661_implies_Equation4131 (G : Type*) [Magma G] (h : Equation1661 G) : Equation4131 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq22 eq18 -- backward demodulation 18,22
  have eq38 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq37 eq10 -- backward demodulation 10,37
  subsumption eq38 rfl


@[equational_result]
theorem Equation1661_implies_Equation4118 (G : Type*) [Magma G] (h : Equation1661 G) : Equation4118 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq22 eq18 -- backward demodulation 18,22
  have eq38 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq37 eq10 -- backward demodulation 10,37
  subsumption eq38 rfl


@[equational_result]
theorem Equation1661_implies_Equation1850 (G : Type*) [Magma G] (h : Equation1661 G) : Equation1850 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq35 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq22 eq18 -- backward demodulation 18,22
  have eq40 : sK0 ≠ sK0 := superpose eq35 eq10 -- superposition 10,35, 35 into 10, unify on (0).2 in 35 and (0).2 in 10
  subsumption eq40 rfl


@[equational_result]
theorem Equation1661_implies_Equation3522 (G : Type*) [Magma G] (h : Equation1661 G) : Equation3522 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq35 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq22 eq18 -- backward demodulation 18,22
  have eq38 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq35 eq10 -- backward demodulation 10,35
  subsumption eq38 rfl


@[equational_result]
theorem Equation1661_implies_Equation1861 (G : Type*) [Magma G] (h : Equation1661 G) : Equation1861 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq35 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq22 eq18 -- backward demodulation 18,22
  have eq40 : sK0 ≠ sK0 := superpose eq35 eq10 -- superposition 10,35, 35 into 10, unify on (0).2 in 35 and (0).2 in 10
  subsumption eq40 rfl


@[equational_result]
theorem Equation1661_implies_Equation2460 (G : Type*) [Magma G] (h : Equation1661 G) : Equation2460 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq35 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq22 eq18 -- backward demodulation 18,22
  have eq38 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq22 eq10 -- backward demodulation 10,22
  subsumption eq38 eq35


@[equational_result]
theorem Equation1661_implies_Equation3526 (G : Type*) [Magma G] (h : Equation1661 G) : Equation3526 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq35 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq22 eq18 -- backward demodulation 18,22
  have eq38 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq35 eq10 -- backward demodulation 10,35
  subsumption eq38 rfl


@[equational_result]
theorem Equation1661_implies_Equation23 (G : Type*) [Magma G] (h : Equation1661 G) : Equation23 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq17 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X1 := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1.2 in 11
  have eq21 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).1.1 in 12
  have eq36 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq21 eq17 -- backward demodulation 17,21
  have eq44 : sK0 ≠ sK0 := superpose eq36 eq9 -- superposition 9,36, 36 into 9, unify on (0).2 in 36 and (0).2 in 9
  subsumption eq44 rfl


@[equational_result]
theorem Equation1661_implies_Equation2446 (G : Type*) [Magma G] (h : Equation1661 G) : Equation2446 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq22 eq18 -- backward demodulation 18,22
  have eq38 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq22 eq10 -- backward demodulation 10,22
  subsumption eq38 eq37


@[equational_result]
theorem Equation2473_implies_Equation1659 (G : Type*) [Magma G] (h : Equation2473 G) : Equation1659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X1) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq19 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq18 eq11 -- backward demodulation 11,18
  have eq27 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq27 rfl


@[equational_result]
theorem Equation2473_implies_Equation1873 (G : Type*) [Magma G] (h : Equation2473 G) : Equation1873 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X1) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq20 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation2473_implies_Equation1657 (G : Type*) [Magma G] (h : Equation2473 G) : Equation1657 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X1) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq19 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq18 eq11 -- backward demodulation 11,18
  have eq27 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq27 rfl


@[equational_result]
theorem Equation2473_implies_Equation3518 (G : Type*) [Magma G] (h : Equation2473 G) : Equation3518 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X1) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq20 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq22 rfl


@[equational_result]
theorem Equation2473_implies_Equation3079 (G : Type*) [Magma G] (h : Equation2473 G) : Equation3079 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X1) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq21 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq21 eq10 -- backward demodulation 10,21
  subsumption eq22 eq21


@[equational_result]
theorem Equation2473_implies_Equation3526 (G : Type*) [Magma G] (h : Equation2473 G) : Equation3526 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X1) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq20 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq22 rfl


@[equational_result]
theorem Equation2473_implies_Equation4135 (G : Type*) [Magma G] (h : Equation2473 G) : Equation4135 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X1) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq21 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation2473_implies_Equation3058 (G : Type*) [Magma G] (h : Equation2473 G) : Equation3058 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X1) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq21 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq21 eq10 -- backward demodulation 10,21
  subsumption eq22 eq21


@[equational_result]
theorem Equation2473_implies_Equation3522 (G : Type*) [Magma G] (h : Equation2473 G) : Equation3522 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X1) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq20 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq22 rfl


@[equational_result]
theorem Equation2473_implies_Equation2485 (G : Type*) [Magma G] (h : Equation2473 G) : Equation2485 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X1) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq20 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq22 eq20


@[equational_result]
theorem Equation2473_implies_Equation1838 (G : Type*) [Magma G] (h : Equation2473 G) : Equation1838 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X1) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq21 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : sK0 ≠ sK0 := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation2473_implies_Equation1850 (G : Type*) [Magma G] (h : Equation2473 G) : Equation1850 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X1) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq20 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation2473_implies_Equation3521 (G : Type*) [Magma G] (h : Equation2473 G) : Equation3521 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X1) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq74 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq74 rfl


@[equational_result]
theorem Equation2473_implies_Equation4073 (G : Type*) [Magma G] (h : Equation2473 G) : Equation4073 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X1) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq21 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq21 eq10 -- backward demodulation 10,21
  subsumption eq22 rfl


@[equational_result]
theorem Equation2473_implies_Equation1630 (G : Type*) [Magma G] (h : Equation2473 G) : Equation1630 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X1) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq20 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq18 eq11 -- backward demodulation 11,18
  have eq27 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq27 rfl


@[equational_result]
theorem Equation2473_implies_Equation3457 (G : Type*) [Magma G] (h : Equation2473 G) : Equation3457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X1) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq64 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq64 rfl


@[equational_result]
theorem Equation2473_implies_Equation3523 (G : Type*) [Magma G] (h : Equation2473 G) : Equation3523 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) ≠ (sK0 ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X1) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq74 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).1 in 10
  subsumption eq74 rfl


@[equational_result]
theorem Equation1659_implies_Equation2473 (G : Type*) [Magma G] (h : Equation1659 G) : Equation2473 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq19 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq19 eq13


@[equational_result]
theorem Equation1663_implies_Equation2463 (G : Type*) [Magma G] (h : Equation1663 G) : Equation2463 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X4 : G) : ((X4 ◇ X0) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq18 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq18 eq13


@[equational_result]
theorem Equation1663_implies_Equation2443 (G : Type*) [Magma G] (h : Equation1663 G) : Equation2443 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X4 : G) : ((X4 ◇ X0) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq18 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq18 eq13


@[equational_result]
theorem Equation1663_implies_Equation3524 (G : Type*) [Magma G] (h : Equation1663 G) : Equation3524 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X4 : G) : ((X4 ◇ X0) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq52 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq52 rfl


@[equational_result]
theorem Equation2477_implies_Equation1839 (G : Type*) [Magma G] (h : Equation2477 G) : Equation1839 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X0 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq16 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X1)) = X3 := superpose eq13 eq11 -- backward demodulation 11,13
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X2)) := superpose eq16 eq16 -- superposition 16,16, 16 into 16, unify on (0).2 in 16 and (0).1.1 in 16
  have eq24 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq24 eq16


@[equational_result]
theorem Equation2477_implies_Equation1663 (G : Type*) [Magma G] (h : Equation2477 G) : Equation1663 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X0 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq16 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X1)) = X3 := superpose eq13 eq11 -- backward demodulation 11,13
  have eq31 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := superpose eq13 eq16 -- superposition 16,13, 13 into 16, unify on (0).2 in 13 and (0).1.1 in 16
  have eq184 : sK0 ≠ sK0 := superpose eq31 eq10 -- superposition 10,31, 31 into 10, unify on (0).2 in 31 and (0).2 in 10
  subsumption eq184 rfl


@[equational_result]
theorem Equation1656_implies_Equation1833 (G : Type*) [Magma G] (h : Equation1656 G) : Equation1833 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.1 in 9
  have eq98 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq98 rfl


@[equational_result]
theorem Equation1656_implies_Equation3527 (G : Type*) [Magma G] (h : Equation1656 G) : Equation3527 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq36 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X2)) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.2.1 in 14
  have eq162 (X0 X1 X3 : G) : (X3 ◇ X0) = (X3 ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).2.2 in 36
  have eq227 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := superpose eq36 eq10 -- superposition 10,36, 36 into 10, unify on (0).2 in 36 and (0).2 in 10
  subsumption eq227 eq162


@[equational_result]
theorem Equation1656_implies_Equation1852 (G : Type*) [Magma G] (h : Equation1656 G) : Equation1852 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.1 in 9
  have eq98 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq98 rfl


@[equational_result]
theorem Equation2489_implies_Equation1851 (G : Type*) [Magma G] (h : Equation2489 G) : Equation1851 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X0 ◇ X5)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X4 : G) : ((X4 ◇ X0) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq18 (X0 X1 X4 X5 : G) : ((X4 ◇ (X0 ◇ X5)) ◇ (X0 ◇ X1)) = X4 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq26 : sK0 ≠ sK0 := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation2489_implies_Equation1656 (G : Type*) [Magma G] (h : Equation2489 G) : Equation1656 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X4 : G) : ((X4 ◇ X0) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq39 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq39 eq12


@[equational_result]
theorem Equation2489_implies_Equation1871 (G : Type*) [Magma G] (h : Equation2489 G) : Equation1871 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X0 ◇ X5)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X4 : G) : ((X4 ◇ X0) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq18 (X0 X1 X4 X5 : G) : ((X4 ◇ (X0 ◇ X5)) ◇ (X0 ◇ X1)) = X4 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq26 : sK0 ≠ sK0 := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation1852_implies_Equation1658 (G : Type*) [Magma G] (h : Equation1852 G) : Equation1658 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 X3 : G) : (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) = (X3 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq30 (X0 X3 : G) : ((X3 ◇ X0) ◇ X0) = X3 := superpose eq19 eq13 -- backward demodulation 13,19
  have eq31 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq30 eq10 -- backward demodulation 10,30
  subsumption eq31 eq30


@[equational_result]
theorem Equation1852_implies_Equation2477 (G : Type*) [Magma G] (h : Equation1852 G) : Equation2477 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 X3 : G) : (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) = (X3 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq31 (X0 X3 : G) : ((X3 ◇ X0) ◇ X0) = X3 := superpose eq19 eq13 -- backward demodulation 13,19
  have eq35 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ X0) := superpose eq31 eq12 -- superposition 12,31, 31 into 12, unify on (0).2 in 31 and (0).2.2 in 12
  have eq39 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq35 eq10 -- backward demodulation 10,35
  subsumption eq39 eq31


@[equational_result]
theorem Equation1852_implies_Equation1860 (G : Type*) [Magma G] (h : Equation1852 G) : Equation1860 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq9


@[equational_result]
theorem Equation2463_implies_Equation4314 (G : Type*) [Magma G] (h : Equation2463 G) : Equation4314 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq40 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ X1) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2.1 in 21
  have eq41 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.1 in 21
  have eq64 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X2)) := superpose eq40 eq41 -- forward demodulation 41,40
  have eq327 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq64 eq10 -- superposition 10,64, 64 into 10, unify on (0).2 in 64 and (0).2 in 10
  subsumption eq327 rfl


@[equational_result]
theorem Equation2463_implies_Equation1837 (G : Type*) [Magma G] (h : Equation2463 G) : Equation1837 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq27 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = X0 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1 in 12
  have eq40 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ X1) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2.1 in 21
  have eq41 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.1 in 21
  have eq64 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X0)) := superpose eq40 eq41 -- forward demodulation 41,40
  have eq66 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := superpose eq64 eq10 -- backward demodulation 10,64
  subsumption eq66 eq27


@[equational_result]
theorem Equation2463_implies_Equation3520 (G : Type*) [Magma G] (h : Equation2463 G) : Equation3520 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) ≠ (sK0 ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq40 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ X1) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2.1 in 21
  have eq202 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq40 eq10 -- superposition 10,40, 40 into 10, unify on (0).2 in 40 and (0).1 in 10
  subsumption eq202 rfl


@[equational_result]
theorem Equation2463_implies_Equation4282 (G : Type*) [Magma G] (h : Equation2463 G) : Equation4282 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq40 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ X1) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2.1 in 21
  have eq41 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.1 in 21
  have eq64 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X0)) := superpose eq40 eq41 -- forward demodulation 41,40
  have eq66 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq64 eq10 -- backward demodulation 10,64
  subsumption eq66 eq64


@[equational_result]
theorem Equation2463_implies_Equation2489 (G : Type*) [Magma G] (h : Equation2463 G) : Equation2489 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK3)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X4))) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq36 (X0 X3 : G) : ((X0 ◇ X3) ◇ X3) = X0 := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).1 in 21
  have eq40 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ X1) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2.1 in 21
  have eq41 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.1 in 21
  have eq53 (X0 X1 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X4))) = X3 := superpose eq40 eq13 -- backward demodulation 13,40
  have eq62 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) = X3 := superpose eq40 eq53 -- forward demodulation 53,40
  have eq64 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X0)) := superpose eq40 eq41 -- forward demodulation 41,40
  have eq66 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) ◇ sK1) := superpose eq64 eq10 -- backward demodulation 10,64
  have eq161 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq62 eq21 -- superposition 21,62, 62 into 21, unify on (0).2 in 62 and (0).2.1 in 21
  have eq175 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq161 eq66 -- backward demodulation 66,161
  subsumption eq175 eq36


@[equational_result]
theorem Equation2463_implies_Equation1874 (G : Type*) [Magma G] (h : Equation2463 G) : Equation1874 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) = (X0 ◇ (X1 ◇ (((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) ◇ X1) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq29 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ X1) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq36 (X0 X3 : G) : ((X0 ◇ X3) ◇ X3) = X0 := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).1 in 21
  have eq40 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ X1) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2.1 in 21
  have eq41 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.1 in 21
  have eq50 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = X0 := superpose eq36 eq29 -- backward demodulation 29,36
  have eq56 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq40 eq26 -- backward demodulation 26,40
  have eq58 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X4))) := superpose eq40 eq15 -- backward demodulation 15,40
  have eq63 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq40 eq58 -- forward demodulation 58,40
  have eq64 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X0)) := superpose eq40 eq41 -- forward demodulation 41,40
  have eq65 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq64 eq63 -- backward demodulation 63,64
  have eq66 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK3)) := superpose eq64 eq10 -- backward demodulation 10,64
  have eq119 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) = X1 := superpose eq36 eq56 -- superposition 56,36, 36 into 56, unify on (0).2 in 36 and (0).1.2.1 in 56
  have eq309 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = X0 := superpose eq65 eq50 -- superposition 50,65, 65 into 50, unify on (0).2 in 65 and (0).1.1 in 50
  have eq331 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) = X0 := superpose eq119 eq309 -- forward demodulation 309,119
  have eq421 (X0 : G) : sK0 ≠ ((sK0 ◇ (sK1 ◇ X0)) ◇ (sK1 ◇ sK3)) := superpose eq64 eq66 -- superposition 66,64, 64 into 66, unify on (0).2 in 64 and (0).2.1 in 66
  subsumption eq421 eq331


@[equational_result]
theorem Equation3084_implies_Equation3074 (G : Type*) [Magma G] (h : Equation3084 G) : Equation3074 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq21 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq24 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK1) ◇ X0) ◇ sK2) ◇ sK3) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq24 eq21


@[equational_result]
theorem Equation3084_implies_Equation3257 (G : Type*) [Magma G] (h : Equation3084 G) : Equation3257 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation3084_implies_Equation4633 (G : Type*) [Magma G] (h : Equation3084 G) : Equation4633 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X3) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq35 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = ((X0 ◇ X2) ◇ X1) := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).1.1 in 12
  have eq58 (X0 X1 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ X0) ◇ X1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq58 eq35


@[equational_result]
theorem Equation3084_implies_Equation3318 (G : Type*) [Magma G] (h : Equation3084 G) : Equation3318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation3084_implies_Equation3091 (G : Type*) [Magma G] (h : Equation3084 G) : Equation3091 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq21 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq24 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ X0) ◇ sK2) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq24 eq21


@[equational_result]
theorem Equation3073_implies_Equation3084 (G : Type*) [Magma G] (h : Equation3073 G) : Equation3084 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq42 (X0 : G) : sK0 ≠ ((((sK0 ◇ X0) ◇ sK0) ◇ sK2) ◇ sK3) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1.1 in 10
  have eq98 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.1 in 9
  have eq105 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ X0) ◇ X3) ◇ X3) := superpose eq98 eq11 -- backward demodulation 11,98
  have eq159 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X4) ◇ X4) = ((((X0 ◇ X0) ◇ X2) ◇ X2) ◇ X3) := superpose eq105 eq105 -- superposition 105,105, 105 into 105, unify on (0).2 in 105 and (0).1.1 in 105
  have eq160 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X0 := superpose eq14 eq105 -- superposition 105,14, 14 into 105, unify on (0).2 in 14 and (0).1 in 105
  have eq199 (X1 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ X1) ◇ X1) ◇ sK3) := superpose eq105 eq42 -- superposition 42,105, 105 into 42, unify on (0).2 in 105 and (0).2.1 in 42
  have eq218 (X0 X2 X3 : G) : ((((X0 ◇ X0) ◇ X2) ◇ X2) ◇ X3) = X0 := superpose eq160 eq159 -- backward demodulation 159,160
  subsumption eq199 eq218


@[equational_result]
theorem Equation3073_implies_Equation3085 (G : Type*) [Magma G] (h : Equation3073 G) : Equation3085 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq55 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.1 in 9
  have eq62 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK2) ◇ sK0) ◇ sK0) := superpose eq55 eq10 -- backward demodulation 10,55
  have eq66 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq55 eq55 -- superposition 55,55, 55 into 55, unify on (0).2 in 55 and (0).2 in 55
  have eq217 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = X0 := superpose eq66 eq14 -- superposition 14,66, 66 into 14, unify on (0).2 in 66 and (0).1.1.1 in 14
  have eq228 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK2) ◇ X0) ◇ sK0) := superpose eq66 eq62 -- superposition 62,66, 66 into 62, unify on (0).2 in 66 and (0).2.1 in 62
  subsumption eq228 eq217


@[equational_result]
theorem Equation3073_implies_Equation3316 (G : Type*) [Magma G] (h : Equation3073 G) : Equation3316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq55 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.1 in 9
  have eq62 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq55 eq10 -- backward demodulation 10,55
  subsumption eq62 eq55


@[equational_result]
theorem Equation3057_implies_Equation3073 (G : Type*) [Magma G] (h : Equation3057 G) : Equation3073 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK2) ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq36 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).1.1 in 9
  have eq39 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ X0) ◇ sK2) ◇ sK2) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.1.1 in 13
  subsumption eq39 eq36


@[equational_result]
theorem Equation3057_implies_Equation3083 (G : Type*) [Magma G] (h : Equation3057 G) : Equation3083 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK2) ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq35 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).1.1 in 9
  have eq40 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ X0) ◇ sK2) ◇ sK2) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.1.1 in 13
  subsumption eq40 eq35


@[equational_result]
theorem Equation3057_implies_Equation3101 (G : Type*) [Magma G] (h : Equation3057 G) : Equation3101 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK3) ◇ sK4) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK2) ◇ sK3) ◇ sK4) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq36 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).1.1 in 9
  have eq39 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ X0) ◇ sK3) ◇ sK4) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.1.1 in 13
  subsumption eq39 eq36


@[equational_result]
theorem Equation3057_implies_Equation3529 (G : Type*) [Magma G] (h : Equation3057 G) : Equation3529 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3057_implies_Equation3071 (G : Type*) [Magma G] (h : Equation3057 G) : Equation3071 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK2) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq36 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).1.1 in 9
  have eq39 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ X0) ◇ sK2) ◇ sK0) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.1.1 in 13
  subsumption eq39 eq36


@[equational_result]
theorem Equation3074_implies_Equation3515 (G : Type*) [Magma G] (h : Equation3074 G) : Equation3515 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ X0) ◇ sK1)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.1 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation3074_implies_Equation4288 (G : Type*) [Magma G] (h : Equation3074 G) : Equation4288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation3074_implies_Equation3058 (G : Type*) [Magma G] (h : Equation3074 G) : Equation3058 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq21 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq24 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK1) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq21


@[equational_result]
theorem Equation3074_implies_Equation3057 (G : Type*) [Magma G] (h : Equation3074 G) : Equation3057 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq21 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq24 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ X0) ◇ sK2) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq24 eq21


@[equational_result]
theorem Equation3074_implies_Equation3509 (G : Type*) [Magma G] (h : Equation3074 G) : Equation3509 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ X0) ◇ sK1)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.1 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation3074_implies_Equation329 (G : Type*) [Magma G] (h : Equation3074 G) : Equation329 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation3063_implies_Equation38 (G : Type*) [Magma G] (h : Equation3063 G) : Equation38 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation3063_implies_Equation329 (G : Type*) [Magma G] (h : Equation3063 G) : Equation329 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3063_implies_Equation3091 (G : Type*) [Magma G] (h : Equation3063 G) : Equation3091 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK2) ◇ sK1) ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1 in 14
  have eq37 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK2) ◇ X0) ◇ sK2) := superpose eq14 eq13 -- superposition 13,14, 14 into 13, unify on (0).2 in 14 and (0).2.1 in 13
  subsumption eq37 eq21


