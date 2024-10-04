import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation749_implies_Equation429 (G : Type*) [Magma G] (h : Equation749 G) : Equation429 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq21 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := superpose eq19 eq10 -- backward demodulation 10,19
  subsumption eq21 eq18


@[equational_result]
theorem Equation749_implies_Equation427 (G : Type*) [Magma G] (h : Equation749 G) : Equation427 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq213 : sK0 ≠ sK0 := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq213 rfl


@[equational_result]
theorem Equation749_implies_Equation2538 (G : Type*) [Magma G] (h : Equation749 G) : Equation2538 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq21 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK2) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq22 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ sK2) := superpose eq19 eq21 -- forward demodulation 21,19
  have eq29 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).1.1 in 13
  have eq37 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X2) = X1 := superpose eq29 eq13 -- backward demodulation 13,29
  have eq46 : sK0 ≠ sK0 := superpose eq37 eq22 -- superposition 22,37, 37 into 22, unify on (0).2 in 37 and (0).2 in 22
  subsumption eq46 rfl


@[equational_result]
theorem Equation749_implies_Equation1117 (G : Type*) [Magma G] (h : Equation749 G) : Equation1117 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X2 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1.1 in 16
  have eq63 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := superpose eq46 eq10 -- backward demodulation 10,46
  subsumption eq63 eq18


@[equational_result]
theorem Equation749_implies_Equation3091 (G : Type*) [Magma G] (h : Equation749 G) : Equation3091 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X2 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1.1 in 16
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X2) = X1 := superpose eq46 eq13 -- backward demodulation 13,46
  have eq63 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK1) ◇ sK2)) ◇ sK2) := superpose eq46 eq10 -- backward demodulation 10,46
  have eq65 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ sK2) := superpose eq19 eq63 -- forward demodulation 63,19
  subsumption eq65 eq58


@[equational_result]
theorem Equation749_implies_Equation562 (G : Type*) [Magma G] (h : Equation749 G) : Equation562 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq21 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := superpose eq19 eq10 -- backward demodulation 10,19
  subsumption eq21 eq18


@[equational_result]
theorem Equation749_implies_Equation556 (G : Type*) [Magma G] (h : Equation749 G) : Equation556 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq213 : sK0 ≠ sK0 := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq213 rfl


@[equational_result]
theorem Equation2928_implies_Equation749 (G : Type*) [Magma G] (h : Equation2928 G) : Equation749 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq25 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := superpose eq18 eq10 -- backward demodulation 10,18
  subsumption eq25 eq13


@[equational_result]
theorem Equation2928_implies_Equation667 (G : Type*) [Magma G] (h : Equation2928 G) : Equation667 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq25 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := superpose eq18 eq10 -- backward demodulation 10,18
  subsumption eq25 eq13


@[equational_result]
theorem Equation2928_implies_Equation4398 (G : Type*) [Magma G] (h : Equation2928 G) : Equation4398 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq40 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq40 rfl


@[equational_result]
theorem Equation2928_implies_Equation707 (G : Type*) [Magma G] (h : Equation2928 G) : Equation707 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq25 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := superpose eq18 eq10 -- backward demodulation 10,18
  subsumption eq25 eq13


@[equational_result]
theorem Equation2928_implies_Equation632 (G : Type*) [Magma G] (h : Equation2928 G) : Equation632 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq25 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := superpose eq18 eq10 -- backward demodulation 10,18
  subsumption eq25 eq13


@[equational_result]
theorem Equation2928_implies_Equation4283 (G : Type*) [Magma G] (h : Equation2928 G) : Equation4283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq25 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq18 eq10 -- backward demodulation 10,18
  subsumption eq25 rfl


@[equational_result]
theorem Equation1571_implies_Equation4491 (G : Type*) [Magma G] (h : Equation1571 G) : Equation4491 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ (X3 ◇ X2)) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X3 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq32 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq38 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq32 -- forward demodulation 32,9
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.2 in 38
  have eq42 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq38 eq38 -- superposition 38,38, 38 into 38, unify on (0).2 in 38 and (0).1.2 in 38
  have eq44 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq38 eq9 -- superposition 9,38, 38 into 9, unify on (0).2 in 38 and (0).1.2 in 9
  have eq52 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq39 eq15 -- backward demodulation 15,39
  have eq55 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq52 eq18 -- backward demodulation 18,52
  have eq63 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq42 eq10 -- backward demodulation 10,42
  have eq296 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq52 eq55 -- superposition 55,52, 52 into 55, unify on (0).2 in 52 and (0).2 in 55
  have eq353 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq38 eq44 -- superposition 44,38, 38 into 44, unify on (0).2 in 38 and (0).1 in 44
  have eq624 (X0 : G) : sK0 ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq296 eq63 -- superposition 63,296, 296 into 63, unify on (0).2 in 296 and (0).2.2 in 63
  subsumption eq624 eq353


@[equational_result]
theorem Equation1571_implies_Equation879 (G : Type*) [Magma G] (h : Equation1571 G) : Equation879 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ (X3 ◇ X2)) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X3 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq32 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq38 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq32 -- forward demodulation 32,9
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.2 in 38
  have eq52 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq39 eq15 -- backward demodulation 15,39
  have eq55 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq52 eq18 -- backward demodulation 18,52
  have eq61 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq55 eq10 -- backward demodulation 10,55
  subsumption eq61 eq38


@[equational_result]
theorem Equation1571_implies_Equation1902 (G : Type*) [Magma G] (h : Equation1571 G) : Equation1902 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ (X3 ◇ X2)) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X3 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq32 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq38 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq32 -- forward demodulation 32,9
  have eq39 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq38 eq10 -- backward demodulation 10,38
  have eq71 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.2 in 38
  have eq78 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq38 eq9 -- superposition 9,38, 38 into 9, unify on (0).2 in 38 and (0).1.2 in 9
  have eq90 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq71 eq15 -- backward demodulation 15,71
  have eq93 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq90 eq18 -- backward demodulation 18,90
  have eq310 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq90 eq93 -- superposition 93,90, 90 into 93, unify on (0).2 in 90 and (0).2 in 93
  have eq366 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq38 eq78 -- superposition 78,38, 38 into 78, unify on (0).2 in 38 and (0).1 in 78
  have eq748 (X0 : G) : sK0 ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq310 eq39 -- superposition 39,310, 310 into 39, unify on (0).2 in 310 and (0).2.2 in 39
  subsumption eq748 eq366


@[equational_result]
theorem Equation1571_implies_Equation4541 (G : Type*) [Magma G] (h : Equation1571 G) : Equation4541 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ (X3 ◇ X2)) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq32 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq38 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq32 -- forward demodulation 32,9
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.2 in 38
  have eq42 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq38 eq38 -- superposition 38,38, 38 into 38, unify on (0).2 in 38 and (0).1.2 in 38
  have eq52 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq39 eq15 -- backward demodulation 15,39
  have eq53 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq52 eq13 -- backward demodulation 13,52
  have eq72 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq53 eq38 -- superposition 38,53, 53 into 38, unify on (0).2 in 53 and (0).1.2 in 38
  have eq85 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK2) ◇ sK1) := superpose eq72 eq10 -- backward demodulation 10,72
  have eq149 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).1.1 in 42
  have eq357 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := superpose eq72 eq85 -- superposition 85,72, 72 into 85, unify on (0).2 in 72 and (0).2 in 85
  subsumption eq357 eq149


@[equational_result]
theorem Equation1571_implies_Equation2737 (G : Type*) [Magma G] (h : Equation1571 G) : Equation2737 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ (X3 ◇ X2)) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq32 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq38 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq32 -- forward demodulation 32,9
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.2 in 38
  have eq52 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq39 eq15 -- backward demodulation 15,39
  have eq53 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq52 eq13 -- backward demodulation 13,52
  have eq61 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq52 eq10 -- backward demodulation 10,52
  have eq73 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq53 eq38 -- superposition 38,53, 53 into 38, unify on (0).2 in 53 and (0).1.2 in 38
  have eq86 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq73 eq61 -- backward demodulation 61,73
  subsumption eq86 eq53


@[equational_result]
theorem Equation1571_implies_Equation3214 (G : Type*) [Magma G] (h : Equation1571 G) : Equation3214 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK2) ◇ sK2) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ (X3 ◇ X2)) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq32 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq38 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq32 -- forward demodulation 32,9
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.2 in 38
  have eq44 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq38 eq9 -- superposition 9,38, 38 into 9, unify on (0).2 in 38 and (0).1.2 in 9
  have eq52 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq39 eq15 -- backward demodulation 15,39
  have eq53 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq52 eq13 -- backward demodulation 13,52
  have eq61 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq53 eq10 -- backward demodulation 10,53
  have eq376 : sK0 ≠ sK0 := superpose eq44 eq61 -- superposition 61,44, 44 into 61, unify on (0).2 in 44 and (0).2 in 61
  subsumption eq376 rfl


@[equational_result]
theorem Equation1571_implies_Equation1887 (G : Type*) [Magma G] (h : Equation1571 G) : Equation1887 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ (X3 ◇ X2)) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq32 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq38 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq32 -- forward demodulation 32,9
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.2 in 38
  have eq42 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq38 eq38 -- superposition 38,38, 38 into 38, unify on (0).2 in 38 and (0).1.2 in 38
  have eq47 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) = X0 := superpose eq38 eq9 -- superposition 9,38, 38 into 9, unify on (0).2 in 38 and (0).1.2.2 in 9
  have eq52 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq39 eq15 -- backward demodulation 15,39
  have eq53 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq52 eq13 -- backward demodulation 13,52
  have eq72 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq53 eq38 -- superposition 38,53, 53 into 38, unify on (0).2 in 53 and (0).1.2 in 38
  have eq85 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := superpose eq72 eq10 -- backward demodulation 10,72
  have eq149 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).1.1 in 42
  have eq158 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := superpose eq149 eq85 -- backward demodulation 85,149
  subsumption eq158 eq47


@[equational_result]
theorem Equation1571_implies_Equation3294 (G : Type*) [Magma G] (h : Equation1571 G) : Equation3294 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ (X3 ◇ X2)) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X3 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq32 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq38 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq32 -- forward demodulation 32,9
  have eq39 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq38 eq10 -- backward demodulation 10,38
  have eq71 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.2 in 38
  have eq90 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq71 eq15 -- backward demodulation 15,71
  have eq93 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq90 eq18 -- backward demodulation 18,90
  have eq309 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq90 eq93 -- superposition 93,90, 90 into 93, unify on (0).2 in 90 and (0).2 in 93
  have eq747 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq309 eq39 -- superposition 39,309, 309 into 39, unify on (0).2 in 309 and (0).2 in 39
  subsumption eq747 eq309


@[equational_result]
theorem Equation1571_implies_Equation546 (G : Type*) [Magma G] (h : Equation1571 G) : Equation546 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ (X3 ◇ X2)) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq32 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq38 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq32 -- forward demodulation 32,9
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.2 in 38
  have eq52 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq39 eq15 -- backward demodulation 15,39
  have eq53 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq52 eq13 -- backward demodulation 13,52
  have eq65 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X2 ◇ X1))) = (X0 ◇ X1) := superpose eq9 eq53 -- superposition 53,9, 9 into 53, unify on (0).2 in 9 and (0).1.1 in 53
  have eq78 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq65 eq10 -- backward demodulation 10,65
  subsumption eq78 eq38


@[equational_result]
theorem Equation1571_implies_Equation2697 (G : Type*) [Magma G] (h : Equation1571 G) : Equation2697 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ (X3 ◇ X2)) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq32 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq38 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq32 -- forward demodulation 32,9
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.2 in 38
  have eq52 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq39 eq15 -- backward demodulation 15,39
  have eq53 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq52 eq13 -- backward demodulation 13,52
  have eq61 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq52 eq10 -- backward demodulation 10,52
  have eq73 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq53 eq38 -- superposition 38,53, 53 into 38, unify on (0).2 in 53 and (0).1.2 in 38
  have eq86 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq73 eq61 -- backward demodulation 61,73
  subsumption eq86 eq53


@[equational_result]
theorem Equation1571_implies_Equation3474 (G : Type*) [Magma G] (h : Equation1571 G) : Equation3474 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ (X3 ◇ X2)) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X3 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq32 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq38 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq32 -- forward demodulation 32,9
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.2 in 38
  have eq42 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq38 eq38 -- superposition 38,38, 38 into 38, unify on (0).2 in 38 and (0).1.2 in 38
  have eq52 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq39 eq15 -- backward demodulation 15,39
  have eq55 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq52 eq18 -- backward demodulation 18,52
  have eq63 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq42 eq10 -- backward demodulation 10,42
  have eq296 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq52 eq55 -- superposition 55,52, 52 into 55, unify on (0).2 in 52 and (0).2 in 55
  have eq624 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq296 eq63 -- superposition 63,296, 296 into 63, unify on (0).2 in 296 and (0).2 in 63
  subsumption eq624 eq296


@[equational_result]
theorem Equation1571_implies_Equation2699 (G : Type*) [Magma G] (h : Equation1571 G) : Equation2699 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ (X3 ◇ X2)) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq32 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq38 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq32 -- forward demodulation 32,9
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.2 in 38
  have eq44 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq38 eq9 -- superposition 9,38, 38 into 9, unify on (0).2 in 38 and (0).1.2 in 9
  have eq52 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq39 eq15 -- backward demodulation 15,39
  have eq53 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq52 eq13 -- backward demodulation 13,52
  have eq72 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq53 eq38 -- superposition 38,53, 53 into 38, unify on (0).2 in 53 and (0).1.2 in 38
  have eq85 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq72 eq10 -- backward demodulation 10,72
  have eq86 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq72 eq85 -- forward demodulation 85,72
  subsumption eq86 eq44


@[equational_result]
theorem Equation1571_implies_Equation4071 (G : Type*) [Magma G] (h : Equation1571 G) : Equation4071 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ (X3 ◇ X2)) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X3 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq32 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq38 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq32 -- forward demodulation 32,9
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.2 in 38
  have eq42 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq38 eq38 -- superposition 38,38, 38 into 38, unify on (0).2 in 38 and (0).1.2 in 38
  have eq52 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq39 eq15 -- backward demodulation 15,39
  have eq55 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq52 eq18 -- backward demodulation 18,52
  have eq63 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq42 eq10 -- backward demodulation 10,42
  have eq296 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq52 eq55 -- superposition 55,52, 52 into 55, unify on (0).2 in 52 and (0).2 in 55
  have eq624 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq296 eq63 -- superposition 63,296, 296 into 63, unify on (0).2 in 296 and (0).2 in 63
  subsumption eq624 eq296


@[equational_result]
theorem Equation1571_implies_Equation3620 (G : Type*) [Magma G] (h : Equation1571 G) : Equation3620 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK2 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ (X3 ◇ X2)) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq32 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq38 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq32 -- forward demodulation 32,9
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.2 in 38
  have eq52 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq39 eq15 -- backward demodulation 15,39
  have eq53 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq52 eq13 -- backward demodulation 13,52
  have eq65 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq9 eq53 -- superposition 53,9, 9 into 53, unify on (0).2 in 9 and (0).1.1 in 53
  have eq72 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq53 eq38 -- superposition 38,53, 53 into 38, unify on (0).2 in 53 and (0).1.2 in 38
  have eq85 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) := superpose eq72 eq10 -- backward demodulation 10,72
  subsumption eq85 eq65


@[equational_result]
theorem Equation1571_implies_Equation883 (G : Type*) [Magma G] (h : Equation1571 G) : Equation883 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ (X3 ◇ X2)) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq32 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq38 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq32 -- forward demodulation 32,9
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.2 in 38
  have eq52 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq39 eq15 -- backward demodulation 15,39
  have eq61 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq52 eq10 -- backward demodulation 10,52
  subsumption eq61 eq38


@[equational_result]
theorem Equation1571_implies_Equation4424 (G : Type*) [Magma G] (h : Equation1571 G) : Equation4424 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ (X3 ◇ X2)) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X3 ◇ X2))) = X3 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq32 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq38 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq32 -- forward demodulation 32,9
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.2 in 38
  have eq44 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq38 eq9 -- superposition 9,38, 38 into 9, unify on (0).2 in 38 and (0).1.2 in 9
  have eq52 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq39 eq15 -- backward demodulation 15,39
  have eq56 (X0 X2 X3 : G) : (X0 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X2))) = X3 := superpose eq52 eq19 -- backward demodulation 19,52
  have eq61 (X0 X3 : G) : (X0 ◇ (X0 ◇ X3)) = X3 := superpose eq52 eq56 -- forward demodulation 56,52
  have eq62 : sK1 ≠ ((sK2 ◇ sK2) ◇ sK1) := superpose eq61 eq10 -- backward demodulation 10,61
  have eq359 : sK1 ≠ sK1 := superpose eq44 eq62 -- superposition 62,44, 44 into 62, unify on (0).2 in 44 and (0).2 in 62
  subsumption eq359 rfl


@[equational_result]
theorem Equation1571_implies_Equation1061 (G : Type*) [Magma G] (h : Equation1571 G) : Equation1061 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ (X3 ◇ X2)) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X3 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq32 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq38 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq32 -- forward demodulation 32,9
  have eq39 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq38 eq10 -- backward demodulation 10,38
  have eq71 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.2 in 38
  have eq78 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq38 eq9 -- superposition 9,38, 38 into 9, unify on (0).2 in 38 and (0).1.2 in 9
  have eq90 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq71 eq15 -- backward demodulation 15,71
  have eq93 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq90 eq18 -- backward demodulation 18,90
  have eq309 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq90 eq93 -- superposition 93,90, 90 into 93, unify on (0).2 in 90 and (0).2 in 93
  have eq365 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq38 eq78 -- superposition 78,38, 38 into 78, unify on (0).2 in 38 and (0).1 in 78
  have eq747 (X0 : G) : sK0 ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq309 eq39 -- superposition 39,309, 309 into 39, unify on (0).2 in 309 and (0).2.2 in 39
  subsumption eq747 eq365


@[equational_result]
theorem Equation1571_implies_Equation3591 (G : Type*) [Magma G] (h : Equation1571 G) : Equation3591 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK0 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ (X3 ◇ X2)) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X3 ◇ X2))) = X3 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq32 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq38 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq32 -- forward demodulation 32,9
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.2 in 38
  have eq42 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq38 eq38 -- superposition 38,38, 38 into 38, unify on (0).2 in 38 and (0).1.2 in 38
  have eq44 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq38 eq9 -- superposition 9,38, 38 into 9, unify on (0).2 in 38 and (0).1.2 in 9
  have eq52 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq39 eq15 -- backward demodulation 15,39
  have eq53 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq52 eq13 -- backward demodulation 13,52
  have eq56 (X0 X2 X3 : G) : (X0 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X2))) = X3 := superpose eq52 eq19 -- backward demodulation 19,52
  have eq61 (X0 X3 : G) : (X0 ◇ (X0 ◇ X3)) = X3 := superpose eq52 eq56 -- forward demodulation 56,52
  have eq72 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq53 eq38 -- superposition 38,53, 53 into 38, unify on (0).2 in 53 and (0).1.2 in 38
  have eq75 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ ((X1 ◇ X3) ◇ X0)) := superpose eq53 eq11 -- superposition 11,53, 53 into 11, unify on (0).2 in 53 and (0).1.2.2 in 11
  have eq85 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := superpose eq72 eq10 -- backward demodulation 10,72
  have eq126 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq61 -- superposition 61,9, 9 into 61, unify on (0).2 in 9 and (0).1.2 in 61
  have eq135 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X1 ◇ (X0 ◇ X3))) := superpose eq126 eq75 -- backward demodulation 75,126
  have eq149 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).1.1 in 42
  have eq158 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := superpose eq149 eq85 -- backward demodulation 85,149
  have eq166 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq38 eq44 -- superposition 44,38, 38 into 44, unify on (0).2 in 38 and (0).1 in 44
  have eq1149 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := superpose eq135 eq158 -- superposition 158,135, 135 into 158, unify on (0).2 in 135 and (0).2 in 158
  have eq1383 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq166 eq1149 -- forward demodulation 1149,166
  subsumption eq1383 eq72


@[equational_result]
theorem Equation1571_implies_Equation3903 (G : Type*) [Magma G] (h : Equation1571 G) : Equation3903 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ (X3 ◇ X2)) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X3 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq32 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq38 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq32 -- forward demodulation 32,9
  have eq39 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq38 eq10 -- backward demodulation 10,38
  have eq71 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.2 in 38
  have eq90 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq71 eq15 -- backward demodulation 15,71
  have eq93 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq90 eq18 -- backward demodulation 18,90
  have eq309 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq90 eq93 -- superposition 93,90, 90 into 93, unify on (0).2 in 90 and (0).2 in 93
  have eq747 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq309 eq39 -- superposition 39,309, 309 into 39, unify on (0).2 in 309 and (0).2 in 39
  subsumption eq747 eq309


@[equational_result]
theorem Equation1571_implies_Equation1334 (G : Type*) [Magma G] (h : Equation1571 G) : Equation1334 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ (X3 ◇ X2)) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq32 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq38 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq32 -- forward demodulation 32,9
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.2 in 38
  have eq46 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq38 eq9 -- superposition 9,38, 38 into 9, unify on (0).2 in 38 and (0).1.1 in 9
  have eq52 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq39 eq15 -- backward demodulation 15,39
  have eq53 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq52 eq13 -- backward demodulation 13,52
  have eq72 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq53 eq38 -- superposition 38,53, 53 into 38, unify on (0).2 in 53 and (0).1.2 in 38
  have eq85 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) := superpose eq72 eq10 -- backward demodulation 10,72
  have eq86 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := superpose eq72 eq85 -- forward demodulation 85,72
  subsumption eq86 eq46


@[equational_result]
theorem Equation2308_implies_Equation4515 (G : Type*) [Magma G] (h : Equation2308 G) : Equation4515 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = ((X2 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (((X3 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X1) ◇ X4) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq19 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq50 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X2 ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq55 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) = X2 := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.1.1.2 in 11
  have eq56 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1.2 in 9
  have eq66 (X1 X2 X3 X4 : G) : (X2 ◇ X1) = (((X3 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X1) ◇ X4) := superpose eq50 eq17 -- backward demodulation 17,50
  have eq70 (X1 X2 X4 : G) : (X2 ◇ X1) = (((X4 ◇ X2) ◇ X1) ◇ X4) := superpose eq50 eq66 -- forward demodulation 66,50
  have eq83 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq56 eq55 -- backward demodulation 55,56
  have eq98 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq12 eq56 -- superposition 56,12, 12 into 56, unify on (0).2 in 12 and (0).1 in 56
  have eq102 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X1))) = (((X0 ◇ X0) ◇ X3) ◇ X1) := superpose eq56 eq12 -- superposition 12,56, 56 into 12, unify on (0).2 in 56 and (0).1.2.2.2 in 12
  have eq107 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = (X1 ◇ (X2 ◇ X3)) := superpose eq56 eq98 -- forward demodulation 98,56
  have eq115 (X1 X2 X4 : G) : (X2 ◇ X1) = ((X2 ◇ (X4 ◇ X1)) ◇ X4) := superpose eq107 eq70 -- backward demodulation 70,107
  have eq137 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X1))) = ((X0 ◇ (X0 ◇ X3)) ◇ X1) := superpose eq107 eq102 -- forward demodulation 102,107
  have eq138 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X0 ◇ X3)) ◇ X1) := superpose eq50 eq137 -- forward demodulation 137,50
  have eq165 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq19 eq83 -- superposition 83,19, 19 into 83, unify on (0).2 in 19 and (0).1.1 in 83
  have eq174 (X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ X3) := superpose eq165 eq138 -- backward demodulation 138,165
  have eq242 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq115 eq19 -- superposition 19,115, 115 into 19, unify on (0).2 in 115 and (0).1.2 in 19
  have eq517 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := superpose eq174 eq10 -- superposition 10,174, 174 into 10, unify on (0).2 in 174 and (0).2 in 10
  subsumption eq517 eq242


@[equational_result]
theorem Equation2308_implies_Equation1764 (G : Type*) [Magma G] (h : Equation2308 G) : Equation1764 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = ((X2 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq50 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X2 ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq54 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.2.2 in 12
  have eq55 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) = X2 := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.1.1.2 in 11
  have eq56 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1.2 in 9
  have eq83 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK0))) := superpose eq54 eq10 -- backward demodulation 10,54
  have eq84 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq56 eq55 -- backward demodulation 55,56
  have eq99 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq12 eq56 -- superposition 56,12, 12 into 56, unify on (0).2 in 12 and (0).1 in 56
  have eq103 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X1))) = (((X0 ◇ X0) ◇ X3) ◇ X1) := superpose eq56 eq12 -- superposition 12,56, 56 into 12, unify on (0).2 in 56 and (0).1.2.2.2 in 12
  have eq108 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = (X1 ◇ (X2 ◇ X3)) := superpose eq56 eq99 -- forward demodulation 99,56
  have eq109 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = (X1 ◇ (X2 ◇ X3)) := superpose eq108 eq12 -- backward demodulation 12,108
  have eq138 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X1))) = ((X0 ◇ (X0 ◇ X3)) ◇ X1) := superpose eq108 eq103 -- forward demodulation 103,108
  have eq139 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X0 ◇ X3)) ◇ X1) := superpose eq50 eq138 -- forward demodulation 138,50
  have eq144 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq19 eq84 -- superposition 84,19, 19 into 84, unify on (0).2 in 19 and (0).1.1 in 84
  have eq149 (X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ X3) := superpose eq144 eq139 -- backward demodulation 139,144
  have eq151 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) := superpose eq149 eq83 -- backward demodulation 83,149
  have eq170 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq19 eq109 -- superposition 109,19, 19 into 109, unify on (0).2 in 19 and (0).1.2.2 in 109
  have eq189 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK1))) := superpose eq170 eq151 -- backward demodulation 151,170
  have eq190 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := superpose eq149 eq189 -- forward demodulation 189,149
  subsumption eq190 eq19


@[equational_result]
theorem Equation2308_implies_Equation4433 (G : Type*) [Magma G] (h : Equation2308 G) : Equation4433 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq19 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq24 : sK1 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq31 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1.2 in 9
  have eq56 : sK1 ≠ sK1 := superpose eq31 eq24 -- superposition 24,31, 31 into 24, unify on (0).2 in 31 and (0).2 in 24
  subsumption eq56 rfl


@[equational_result]
theorem Equation2308_implies_Equation1526 (G : Type*) [Magma G] (h : Equation2308 G) : Equation1526 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq19 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq24 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq31 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1.2 in 9
  have eq59 : sK0 ≠ sK0 := superpose eq31 eq24 -- superposition 24,31, 31 into 24, unify on (0).2 in 31 and (0).2 in 24
  subsumption eq59 rfl


@[equational_result]
theorem Equation2308_implies_Equation1429 (G : Type*) [Magma G] (h : Equation2308 G) : Equation1429 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq19 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq56 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1.2 in 9
  have eq99 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq19 eq56 -- superposition 56,19, 19 into 56, unify on (0).2 in 19 and (0).1 in 56
  have eq138 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq99 eq10 -- backward demodulation 10,99
  subsumption eq138 eq56


@[equational_result]
theorem Equation2308_implies_Equation4477 (G : Type*) [Magma G] (h : Equation2308 G) : Equation4477 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = ((X2 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq21 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) ◇ (X4 ◇ X1)) = ((X2 ◇ X4) ◇ X3) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq24 (X1 X2 X3 X4 : G) : ((X2 ◇ X4) ◇ X3) = (((X2 ◇ X1) ◇ X3) ◇ (X4 ◇ X1)) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq35 (X1 X2 X3 X4 : G) : ((((X2 ◇ X1) ◇ X3) ◇ (X4 ◇ X1)) ◇ (X2 ◇ X3)) = X4 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.1 in 11
  have eq49 (X2 X3 X4 : G) : (((X2 ◇ X4) ◇ X3) ◇ (X2 ◇ X3)) = X4 := superpose eq24 eq35 -- forward demodulation 35,24
  have eq50 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X2 ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq55 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) = X2 := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.1.1.2 in 11
  have eq56 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1.2 in 9
  have eq62 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq83 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq56 eq55 -- backward demodulation 55,56
  have eq85 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq83 eq10 -- backward demodulation 10,83
  have eq105 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq62 eq49 -- superposition 49,62, 62 into 49, unify on (0).2 in 62 and (0).1.1 in 49
  have eq256 : sK0 ≠ sK0 := superpose eq105 eq85 -- superposition 85,105, 105 into 85, unify on (0).2 in 105 and (0).2 in 85
  subsumption eq256 rfl


@[equational_result]
theorem Equation2308_implies_Equation3868 (G : Type*) [Magma G] (h : Equation2308 G) : Equation3868 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq19 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq24 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq31 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1.2 in 9
  have eq57 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq31 eq19 -- superposition 19,31, 31 into 19, unify on (0).2 in 31 and (0).1.2 in 19
  have eq212 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq57 eq24 -- superposition 24,57, 57 into 24, unify on (0).2 in 57 and (0).2 in 24
  subsumption eq212 eq57


@[equational_result]
theorem Equation2308_implies_Equation2340 (G : Type*) [Magma G] (h : Equation2308 G) : Equation2340 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq19 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq24 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq31 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1.2 in 9
  have eq56 : sK0 ≠ sK0 := superpose eq31 eq24 -- superposition 24,31, 31 into 24, unify on (0).2 in 31 and (0).2 in 24
  subsumption eq56 rfl


@[equational_result]
theorem Equation2308_implies_Equation1252 (G : Type*) [Magma G] (h : Equation2308 G) : Equation1252 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = ((X2 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq21 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) ◇ (X4 ◇ X1)) = ((X2 ◇ X4) ◇ X3) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq24 (X1 X2 X3 X4 : G) : ((X2 ◇ X4) ◇ X3) = (((X2 ◇ X1) ◇ X3) ◇ (X4 ◇ X1)) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq35 (X1 X2 X3 X4 : G) : ((((X2 ◇ X1) ◇ X3) ◇ (X4 ◇ X1)) ◇ (X2 ◇ X3)) = X4 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.1 in 11
  have eq49 (X2 X3 X4 : G) : (((X2 ◇ X4) ◇ X3) ◇ (X2 ◇ X3)) = X4 := superpose eq24 eq35 -- forward demodulation 35,24
  have eq50 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X2 ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq62 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq70 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq62 eq10 -- backward demodulation 10,62
  have eq105 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq62 eq49 -- superposition 49,62, 62 into 49, unify on (0).2 in 62 and (0).1.1 in 49
  have eq256 : sK0 ≠ sK0 := superpose eq105 eq70 -- superposition 70,105, 105 into 70, unify on (0).2 in 105 and (0).2 in 70
  subsumption eq256 rfl


@[equational_result]
theorem Equation2308_implies_Equation543 (G : Type*) [Magma G] (h : Equation2308 G) : Equation543 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = ((X2 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq54 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.2.2 in 12
  have eq56 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1.2 in 9
  have eq98 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq12 eq56 -- superposition 56,12, 12 into 56, unify on (0).2 in 12 and (0).1 in 56
  have eq107 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = (X1 ◇ (X2 ◇ X3)) := superpose eq56 eq98 -- forward demodulation 98,56
  have eq108 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = (X1 ◇ (X2 ◇ X3)) := superpose eq107 eq12 -- backward demodulation 12,107
  have eq147 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq19 eq108 -- superposition 108,19, 19 into 108, unify on (0).2 in 19 and (0).1.2.2 in 108
  have eq159 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2))) := superpose eq147 eq10 -- backward demodulation 10,147
  have eq160 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := superpose eq54 eq159 -- forward demodulation 159,54
  have eq161 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := superpose eq147 eq160 -- forward demodulation 160,147
  have eq162 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq19 eq161 -- forward demodulation 161,19
  subsumption eq162 eq19


@[equational_result]
theorem Equation2308_implies_Equation4469 (G : Type*) [Magma G] (h : Equation2308 G) : Equation4469 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = ((X2 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq21 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) ◇ (X4 ◇ X1)) = ((X2 ◇ X4) ◇ X3) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq24 (X1 X2 X3 X4 : G) : ((X2 ◇ X4) ◇ X3) = (((X2 ◇ X1) ◇ X3) ◇ (X4 ◇ X1)) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq35 (X1 X2 X3 X4 : G) : ((((X2 ◇ X1) ◇ X3) ◇ (X4 ◇ X1)) ◇ (X2 ◇ X3)) = X4 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.1 in 11
  have eq49 (X2 X3 X4 : G) : (((X2 ◇ X4) ◇ X3) ◇ (X2 ◇ X3)) = X4 := superpose eq24 eq35 -- forward demodulation 35,24
  have eq50 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X2 ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq62 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq70 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq62 eq10 -- backward demodulation 10,62
  have eq105 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq62 eq49 -- superposition 49,62, 62 into 49, unify on (0).2 in 62 and (0).1.1 in 49
  have eq256 : sK0 ≠ sK0 := superpose eq105 eq70 -- superposition 70,105, 105 into 70, unify on (0).2 in 105 and (0).2 in 70
  subsumption eq256 rfl


@[equational_result]
theorem Equation2308_implies_Equation3607 (G : Type*) [Magma G] (h : Equation2308 G) : Equation3607 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = ((X2 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq50 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X2 ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.2.2 in 12
  have eq55 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) = X2 := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.1.1.2 in 11
  have eq56 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1.2 in 9
  have eq83 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) := superpose eq54 eq10 -- backward demodulation 10,54
  have eq84 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq56 eq55 -- backward demodulation 55,56
  have eq101 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq12 eq56 -- superposition 56,12, 12 into 56, unify on (0).2 in 12 and (0).1 in 56
  have eq105 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X1))) = (((X0 ◇ X0) ◇ X3) ◇ X1) := superpose eq56 eq12 -- superposition 12,56, 56 into 12, unify on (0).2 in 56 and (0).1.2.2.2 in 12
  have eq110 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = (X1 ◇ (X2 ◇ X3)) := superpose eq56 eq101 -- forward demodulation 101,56
  have eq111 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = (X1 ◇ (X2 ◇ X3)) := superpose eq110 eq12 -- backward demodulation 12,110
  have eq139 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X1))) = ((X0 ◇ (X0 ◇ X3)) ◇ X1) := superpose eq110 eq105 -- forward demodulation 105,110
  have eq140 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X0 ◇ X3)) ◇ X1) := superpose eq50 eq139 -- forward demodulation 139,50
  have eq145 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq19 eq84 -- superposition 84,19, 19 into 84, unify on (0).2 in 19 and (0).1.1 in 84
  have eq150 (X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ X3) := superpose eq145 eq140 -- backward demodulation 140,145
  have eq152 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := superpose eq150 eq83 -- backward demodulation 83,150
  have eq171 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq19 eq111 -- superposition 111,19, 19 into 111, unify on (0).2 in 19 and (0).1.2.2 in 111
  have eq2603 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := superpose eq171 eq152 -- superposition 152,171, 171 into 152, unify on (0).2 in 171 and (0).2 in 152
  have eq2769 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := superpose eq54 eq2603 -- forward demodulation 2603,54
  have eq2770 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := superpose eq171 eq2769 -- forward demodulation 2769,171
  have eq2771 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq19 eq2770 -- forward demodulation 2770,19
  subsumption eq2771 rfl


@[equational_result]
theorem Equation2308_implies_Equation3973 (G : Type*) [Magma G] (h : Equation2308 G) : Equation3973 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = ((X2 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq50 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X2 ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq56 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1.2 in 9
  have eq62 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq90 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X3))) = (((X2 ◇ X1) ◇ X3) ◇ X0) := superpose eq12 eq62 -- superposition 62,12, 12 into 62, unify on (0).2 in 12 and (0).1.1 in 62
  have eq98 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq12 eq56 -- superposition 56,12, 12 into 56, unify on (0).2 in 12 and (0).1 in 56
  have eq107 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = (X1 ◇ (X2 ◇ X3)) := superpose eq56 eq98 -- forward demodulation 98,56
  have eq108 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = (X1 ◇ (X2 ◇ X3)) := superpose eq107 eq12 -- backward demodulation 12,107
  have eq117 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X3))) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := superpose eq107 eq90 -- backward demodulation 90,107
  have eq147 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq19 eq108 -- superposition 108,19, 19 into 108, unify on (0).2 in 19 and (0).1.2.2 in 108
  have eq159 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := superpose eq147 eq10 -- backward demodulation 10,147
  have eq472 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := superpose eq117 eq159 -- superposition 159,117, 117 into 159, unify on (0).2 in 117 and (0).2 in 159
  have eq533 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq19 eq472 -- forward demodulation 472,19
  subsumption eq533 rfl


@[equational_result]
theorem Equation2308_implies_Equation1571 (G : Type*) [Magma G] (h : Equation2308 G) : Equation1571 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = ((X2 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq50 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X2 ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq55 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) = X2 := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.1.1.2 in 11
  have eq56 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1.2 in 9
  have eq83 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq56 eq55 -- backward demodulation 55,56
  have eq98 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq12 eq56 -- superposition 56,12, 12 into 56, unify on (0).2 in 12 and (0).1 in 56
  have eq102 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X1))) = (((X0 ◇ X0) ◇ X3) ◇ X1) := superpose eq56 eq12 -- superposition 12,56, 56 into 12, unify on (0).2 in 56 and (0).1.2.2.2 in 12
  have eq107 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = (X1 ◇ (X2 ◇ X3)) := superpose eq56 eq98 -- forward demodulation 98,56
  have eq108 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = (X1 ◇ (X2 ◇ X3)) := superpose eq107 eq12 -- backward demodulation 12,107
  have eq137 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X1))) = ((X0 ◇ (X0 ◇ X3)) ◇ X1) := superpose eq107 eq102 -- forward demodulation 102,107
  have eq138 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X0 ◇ X3)) ◇ X1) := superpose eq50 eq137 -- forward demodulation 137,50
  have eq147 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq19 eq108 -- superposition 108,19, 19 into 108, unify on (0).2 in 19 and (0).1.2.2 in 108
  have eq159 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK1))) := superpose eq147 eq10 -- backward demodulation 10,147
  have eq166 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq19 eq83 -- superposition 83,19, 19 into 83, unify on (0).2 in 19 and (0).1.1 in 83
  have eq175 (X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ X3) := superpose eq166 eq138 -- backward demodulation 138,166
  have eq177 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := superpose eq175 eq159 -- backward demodulation 159,175
  subsumption eq177 eq19


@[equational_result]
theorem Equation2308_implies_Equation1323 (G : Type*) [Magma G] (h : Equation2308 G) : Equation1323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq19 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq54 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  have eq57 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1.2 in 9
  have eq207 : sK0 ≠ sK0 := superpose eq57 eq54 -- superposition 54,57, 57 into 54, unify on (0).2 in 57 and (0).2 in 54
  subsumption eq207 rfl


@[equational_result]
theorem Equation2308_implies_Equation4497 (G : Type*) [Magma G] (h : Equation2308 G) : Equation4497 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = ((X2 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq21 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) ◇ (X4 ◇ X1)) = ((X2 ◇ X4) ◇ X3) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq24 (X1 X2 X3 X4 : G) : ((X2 ◇ X4) ◇ X3) = (((X2 ◇ X1) ◇ X3) ◇ (X4 ◇ X1)) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq35 (X1 X2 X3 X4 : G) : ((((X2 ◇ X1) ◇ X3) ◇ (X4 ◇ X1)) ◇ (X2 ◇ X3)) = X4 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.1 in 11
  have eq49 (X2 X3 X4 : G) : (((X2 ◇ X4) ◇ X3) ◇ (X2 ◇ X3)) = X4 := superpose eq24 eq35 -- forward demodulation 35,24
  have eq50 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X2 ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq56 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1.2 in 9
  have eq62 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq85 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq56 eq10 -- backward demodulation 10,56
  have eq105 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq62 eq49 -- superposition 49,62, 62 into 49, unify on (0).2 in 62 and (0).1.1 in 49
  have eq266 : sK0 ≠ sK0 := superpose eq105 eq85 -- superposition 85,105, 105 into 85, unify on (0).2 in 105 and (0).2 in 85
  subsumption eq266 rfl


@[equational_result]
theorem Equation2308_implies_Equation2043 (G : Type*) [Magma G] (h : Equation2308 G) : Equation2043 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = ((X2 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq50 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X2 ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq54 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.2.2 in 12
  have eq55 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) = X2 := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.1.1.2 in 11
  have eq56 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1.2 in 9
  have eq83 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) := superpose eq54 eq10 -- backward demodulation 10,54
  have eq84 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq56 eq55 -- backward demodulation 55,56
  have eq99 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq12 eq56 -- superposition 56,12, 12 into 56, unify on (0).2 in 12 and (0).1 in 56
  have eq100 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq19 eq56 -- superposition 56,19, 19 into 56, unify on (0).2 in 19 and (0).1 in 56
  have eq103 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X1))) = (((X0 ◇ X0) ◇ X3) ◇ X1) := superpose eq56 eq12 -- superposition 12,56, 56 into 12, unify on (0).2 in 56 and (0).1.2.2.2 in 12
  have eq108 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = (X1 ◇ (X2 ◇ X3)) := superpose eq56 eq99 -- forward demodulation 99,56
  have eq138 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq100 eq83 -- backward demodulation 83,100
  have eq139 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X1))) = ((X0 ◇ (X0 ◇ X3)) ◇ X1) := superpose eq108 eq103 -- forward demodulation 103,108
  have eq140 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X0 ◇ X3)) ◇ X1) := superpose eq50 eq139 -- forward demodulation 139,50
  have eq145 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq19 eq84 -- superposition 84,19, 19 into 84, unify on (0).2 in 19 and (0).1.1 in 84
  have eq150 (X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ X3) := superpose eq145 eq140 -- backward demodulation 140,145
  have eq152 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq150 eq138 -- backward demodulation 138,150
  subsumption eq152 eq19


@[equational_result]
theorem Equation2308_implies_Equation2076 (G : Type*) [Magma G] (h : Equation2308 G) : Equation2076 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = ((X2 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq50 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X2 ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq54 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.2.2 in 12
  have eq55 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) = X2 := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.1.1.2 in 11
  have eq56 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1.2 in 9
  have eq61 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)) = X2 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1.2.2 in 9
  have eq83 : sK0 ≠ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2)) := superpose eq54 eq10 -- backward demodulation 10,54
  have eq84 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq56 eq55 -- backward demodulation 55,56
  have eq99 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq12 eq56 -- superposition 56,12, 12 into 56, unify on (0).2 in 12 and (0).1 in 56
  have eq103 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X1))) = (((X0 ◇ X0) ◇ X3) ◇ X1) := superpose eq56 eq12 -- superposition 12,56, 56 into 12, unify on (0).2 in 56 and (0).1.2.2.2 in 12
  have eq108 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = (X1 ◇ (X2 ◇ X3)) := superpose eq56 eq99 -- forward demodulation 99,56
  have eq138 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X1))) = ((X0 ◇ (X0 ◇ X3)) ◇ X1) := superpose eq108 eq103 -- forward demodulation 103,108
  have eq139 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X0 ◇ X3)) ◇ X1) := superpose eq50 eq138 -- forward demodulation 138,50
  have eq144 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq19 eq84 -- superposition 84,19, 19 into 84, unify on (0).2 in 19 and (0).1.1 in 84
  have eq149 (X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ X3) := superpose eq144 eq139 -- backward demodulation 139,144
  have eq151 : sK0 ≠ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) := superpose eq149 eq83 -- backward demodulation 83,149
  subsumption eq151 eq61


@[equational_result]
theorem Equation1334_implies_Equation3675 (G : Type*) [Magma G] (h : Equation1334 G) : Equation3675 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.1.1 in 12
  have eq55 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1))) = X2 := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.2.2.1 in 11
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.1 in 12
  have eq62 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq84 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq56 eq55 -- backward demodulation 55,56
  have eq86 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq54 eq57 -- forward demodulation 57,54
  have eq87 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq84 eq86 -- forward demodulation 86,84
  have eq133 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq62 eq84 -- superposition 84,62, 62 into 84, unify on (0).2 in 62 and (0).1.2 in 84
  have eq141 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := superpose eq133 eq10 -- backward demodulation 10,133
  subsumption eq141 eq87


@[equational_result]
theorem Equation1334_implies_Equation1264 (G : Type*) [Magma G] (h : Equation1334 G) : Equation1264 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq24 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq31 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq59 : sK0 ≠ sK0 := superpose eq31 eq24 -- superposition 24,31, 31 into 24, unify on (0).2 in 31 and (0).2 in 24
  subsumption eq59 rfl


@[equational_result]
theorem Equation1334_implies_Equation4106 (G : Type*) [Magma G] (h : Equation1334 G) : Equation4106 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq24 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq31 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq57 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq31 eq19 -- superposition 19,31, 31 into 19, unify on (0).2 in 31 and (0).1.1 in 19
  have eq227 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq57 eq24 -- superposition 24,57, 57 into 24, unify on (0).2 in 57 and (0).2 in 24
  subsumption eq227 eq57


@[equational_result]
theorem Equation1334_implies_Equation1726 (G : Type*) [Magma G] (h : Equation1334 G) : Equation1726 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ ((((X0 ◇ X1) ◇ X4) ◇ X2) ◇ X4)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq35 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X3 ◇ X4) ◇ (X0 ◇ (X3 ◇ X1)))) = X4 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq49 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X4 ◇ X1))) = X4 := superpose eq24 eq35 -- forward demodulation 35,24
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.1.1 in 12
  have eq55 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1))) = X2 := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.2.2.1 in 11
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.1 in 12
  have eq62 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq84 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ sK0))) := superpose eq54 eq10 -- backward demodulation 10,54
  have eq85 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq56 eq55 -- backward demodulation 55,56
  have eq87 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq85 eq84 -- backward demodulation 84,85
  have eq88 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq54 eq57 -- forward demodulation 57,54
  have eq89 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ X0) := superpose eq85 eq88 -- forward demodulation 88,85
  have eq112 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq62 eq49 -- superposition 49,62, 62 into 49, unify on (0).2 in 62 and (0).1.2 in 49
  have eq253 (X0 : G) : sK0 ≠ ((X0 ◇ X0) ◇ sK0) := superpose eq89 eq87 -- superposition 87,89, 89 into 87, unify on (0).2 in 89 and (0).2.1 in 87
  subsumption eq253 eq112


@[equational_result]
theorem Equation1334_implies_Equation825 (G : Type*) [Magma G] (h : Equation1334 G) : Equation825 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X1) ◇ X3)) = (X4 ◇ (X2 ◇ (((X4 ◇ X5) ◇ X0) ◇ X5))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.1.1 in 12
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq64 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) = (X2 ◇ X0) := superpose eq50 eq13 -- backward demodulation 13,50
  have eq65 (X0 X1 X2 X4 X5 : G) : (X4 ◇ (X2 ◇ (((X4 ◇ X5) ◇ X0) ◇ X5))) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq50 eq14 -- backward demodulation 14,50
  have eq70 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq50 eq64 -- forward demodulation 64,50
  have eq71 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = (X4 ◇ (X2 ◇ (X0 ◇ X4))) := superpose eq50 eq65 -- forward demodulation 65,50
  have eq72 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq70 eq71 -- forward demodulation 71,70
  have eq84 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := superpose eq54 eq10 -- backward demodulation 10,54
  have eq85 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq72 eq84 -- forward demodulation 84,72
  have eq132 : sK0 ≠ sK0 := superpose eq56 eq85 -- superposition 85,56, 56 into 85, unify on (0).2 in 56 and (0).2 in 85
  subsumption eq132 rfl


@[equational_result]
theorem Equation1334_implies_Equation2308 (G : Type*) [Magma G] (h : Equation1334 G) : Equation2308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ ((((X0 ◇ X1) ◇ X4) ◇ X2) ◇ X4)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq35 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X3 ◇ X4) ◇ (X0 ◇ (X3 ◇ X1)))) = X4 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq49 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X4 ◇ X1))) = X4 := superpose eq24 eq35 -- forward demodulation 35,24
  have eq55 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1))) = X2 := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.2.2.1 in 11
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq84 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq56 eq55 -- backward demodulation 55,56
  have eq121 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq56 eq49 -- superposition 49,56, 56 into 49, unify on (0).2 in 56 and (0).1 in 49
  have eq124 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq49 eq19 -- superposition 19,49, 49 into 19, unify on (0).2 in 49 and (0).1.1 in 19
  have eq132 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ sK2) := superpose eq124 eq10 -- backward demodulation 10,124
  have eq133 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK2) := superpose eq84 eq132 -- forward demodulation 132,84
  subsumption eq133 eq121


@[equational_result]
theorem Equation1334_implies_Equation2389 (G : Type*) [Magma G] (h : Equation1334 G) : Equation2389 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ ((((X0 ◇ X1) ◇ X4) ◇ X2) ◇ X4)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq35 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X3 ◇ X4) ◇ (X0 ◇ (X3 ◇ X1)))) = X4 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq49 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X4 ◇ X1))) = X4 := superpose eq24 eq35 -- forward demodulation 35,24
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.1.1 in 12
  have eq55 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1))) = X2 := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.2.2.1 in 11
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.1 in 12
  have eq62 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq70 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq62 eq10 -- backward demodulation 10,62
  have eq85 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq56 eq55 -- backward demodulation 55,56
  have eq87 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq54 eq57 -- forward demodulation 57,54
  have eq88 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ X0) := superpose eq85 eq87 -- forward demodulation 87,85
  have eq111 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq62 eq49 -- superposition 49,62, 62 into 49, unify on (0).2 in 62 and (0).1.2 in 49
  have eq252 (X0 : G) : sK0 ≠ ((X0 ◇ X0) ◇ sK0) := superpose eq88 eq70 -- superposition 70,88, 88 into 70, unify on (0).2 in 88 and (0).2.1 in 70
  subsumption eq252 eq111


@[equational_result]
theorem Equation1334_implies_Equation3573 (G : Type*) [Magma G] (h : Equation1334 G) : Equation3573 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK2 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.1.1 in 12
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq64 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) = (X2 ◇ X0) := superpose eq50 eq13 -- backward demodulation 13,50
  have eq70 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq50 eq64 -- forward demodulation 64,50
  have eq84 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := superpose eq54 eq10 -- backward demodulation 10,54
  have eq87 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq56 eq84 -- backward demodulation 84,56
  have eq139 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq56 eq70 -- superposition 70,56, 56 into 70, unify on (0).2 in 56 and (0).2.2 in 70
  have eq765 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq139 eq87 -- superposition 87,139, 139 into 87, unify on (0).2 in 139 and (0).2 in 87
  subsumption eq765 rfl


@[equational_result]
theorem Equation1334_implies_Equation1451 (G : Type*) [Magma G] (h : Equation1334 G) : Equation1451 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ ((((X0 ◇ X1) ◇ X4) ◇ X2) ◇ X4)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq35 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X3 ◇ X4) ◇ (X0 ◇ (X3 ◇ X1)))) = X4 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq49 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X4 ◇ X1))) = X4 := superpose eq24 eq35 -- forward demodulation 35,24
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq86 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq56 eq10 -- backward demodulation 10,56
  have eq122 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq49 eq56 -- superposition 56,49, 49 into 56, unify on (0).2 in 49 and (0).1 in 56
  have eq503 : sK0 ≠ sK0 := superpose eq122 eq86 -- superposition 86,122, 122 into 86, unify on (0).2 in 122 and (0).2 in 86
  subsumption eq503 rfl


@[equational_result]
theorem Equation1334_implies_Equation716 (G : Type*) [Magma G] (h : Equation1334 G) : Equation716 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.1.1 in 12
  have eq62 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq64 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) = (X2 ◇ X0) := superpose eq50 eq13 -- backward demodulation 13,50
  have eq70 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq50 eq64 -- forward demodulation 64,50
  have eq84 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := superpose eq54 eq10 -- backward demodulation 10,54
  have eq85 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq70 eq84 -- forward demodulation 84,70
  subsumption eq85 eq62


@[equational_result]
theorem Equation1334_implies_Equation3497 (G : Type*) [Magma G] (h : Equation1334 G) : Equation3497 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq24 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq31 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq57 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq31 eq19 -- superposition 19,31, 31 into 19, unify on (0).2 in 31 and (0).1.1 in 19
  have eq227 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq57 eq24 -- superposition 24,57, 57 into 24, unify on (0).2 in 57 and (0).2 in 24
  subsumption eq227 eq57


@[equational_result]
theorem Equation1334_implies_Equation4525 (G : Type*) [Magma G] (h : Equation1334 G) : Equation4525 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq55 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1))) = X2 := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.2.2.1 in 11
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq62 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq64 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) = (X2 ◇ X0) := superpose eq50 eq13 -- backward demodulation 13,50
  have eq70 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq50 eq64 -- forward demodulation 64,50
  have eq84 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq56 eq55 -- backward demodulation 55,56
  have eq133 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq62 eq84 -- superposition 84,62, 62 into 84, unify on (0).2 in 62 and (0).1.2 in 84
  have eq141 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq133 eq10 -- backward demodulation 10,133
  have eq215 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ X0)) := superpose eq70 eq84 -- superposition 84,70, 70 into 84, unify on (0).2 in 70 and (0).1.2 in 84
  have eq443 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK0 ◇ sK1)) := superpose eq133 eq141 -- superposition 141,133, 133 into 141, unify on (0).2 in 133 and (0).2 in 141
  subsumption eq443 eq215


@[equational_result]
theorem Equation1334_implies_Equation2304 (G : Type*) [Magma G] (h : Equation1334 G) : Equation2304 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq58 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq58 eq56


@[equational_result]
theorem Equation1334_implies_Equation1086 (G : Type*) [Magma G] (h : Equation1334 G) : Equation1086 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.1.1 in 12
  have eq62 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq64 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) = (X2 ◇ X0) := superpose eq50 eq13 -- backward demodulation 13,50
  have eq70 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq50 eq64 -- forward demodulation 64,50
  have eq84 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0))) := superpose eq54 eq10 -- backward demodulation 10,54
  have eq85 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := superpose eq54 eq84 -- forward demodulation 84,54
  have eq86 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq70 eq85 -- forward demodulation 85,70
  subsumption eq86 eq62


@[equational_result]
theorem Equation1334_implies_Equation452 (G : Type*) [Magma G] (h : Equation1334 G) : Equation452 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq62 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq70 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq62 eq10 -- backward demodulation 10,62
  have eq131 : sK0 ≠ sK0 := superpose eq56 eq70 -- superposition 70,56, 56 into 70, unify on (0).2 in 56 and (0).2 in 70
  subsumption eq131 rfl


@[equational_result]
theorem Equation1334_implies_Equation2660 (G : Type*) [Magma G] (h : Equation1334 G) : Equation2660 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X1) ◇ X3)) = (X4 ◇ (X2 ◇ (((X4 ◇ X5) ◇ X0) ◇ X5))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq64 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) = (X2 ◇ X0) := superpose eq50 eq13 -- backward demodulation 13,50
  have eq65 (X0 X1 X2 X4 X5 : G) : (X4 ◇ (X2 ◇ (((X4 ◇ X5) ◇ X0) ◇ X5))) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq50 eq14 -- backward demodulation 14,50
  have eq70 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq50 eq64 -- forward demodulation 64,50
  have eq71 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = (X4 ◇ (X2 ◇ (X0 ◇ X4))) := superpose eq50 eq65 -- forward demodulation 65,50
  have eq72 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq70 eq71 -- forward demodulation 71,70
  have eq73 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq72 eq10 -- backward demodulation 10,72
  subsumption eq73 eq19


@[equational_result]
theorem Equation1334_implies_Equation1898 (G : Type*) [Magma G] (h : Equation1334 G) : Equation1898 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq62 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq70 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq62 eq10 -- backward demodulation 10,62
  have eq131 : sK0 ≠ sK0 := superpose eq56 eq70 -- superposition 70,56, 56 into 70, unify on (0).2 in 56 and (0).2 in 70
  subsumption eq131 rfl


@[equational_result]
theorem Equation1334_implies_Equation3558 (G : Type*) [Magma G] (h : Equation1334 G) : Equation3558 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.1.1 in 12
  have eq64 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) = (X2 ◇ X0) := superpose eq50 eq13 -- backward demodulation 13,50
  have eq70 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq50 eq64 -- forward demodulation 64,50
  have eq84 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := superpose eq54 eq10 -- backward demodulation 10,54
  subsumption eq84 eq70


@[equational_result]
theorem Equation1334_implies_Equation4143 (G : Type*) [Magma G] (h : Equation1334 G) : Equation4143 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq20 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ ((((X0 ◇ X1) ◇ X4) ◇ X2) ◇ X4)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq12 eq20 -- forward demodulation 20,12
  have eq35 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X3 ◇ X4) ◇ (X0 ◇ (X3 ◇ X1)))) = X4 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq49 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X4 ◇ X1))) = X4 := superpose eq24 eq35 -- forward demodulation 35,24
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.1.1 in 12
  have eq55 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1))) = X2 := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.2.2.1 in 11
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq62 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq64 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) = (X2 ◇ X0) := superpose eq50 eq13 -- backward demodulation 13,50
  have eq70 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq50 eq64 -- forward demodulation 64,50
  have eq84 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK2) := superpose eq54 eq10 -- backward demodulation 10,54
  have eq85 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq56 eq55 -- backward demodulation 55,56
  have eq111 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq62 eq85 -- superposition 85,62, 62 into 85, unify on (0).2 in 62 and (0).1.2 in 85
  have eq115 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK2) := superpose eq111 eq84 -- backward demodulation 84,111
  have eq157 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq49 eq19 -- superposition 19,49, 49 into 19, unify on (0).2 in 49 and (0).1.1 in 19
  have eq196 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := superpose eq157 eq115 -- backward demodulation 115,157
  have eq310 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := superpose eq111 eq196 -- superposition 196,111, 111 into 196, unify on (0).2 in 111 and (0).2 in 196
  subsumption eq310 eq70


@[equational_result]
theorem Equation1334_implies_Equation4461 (G : Type*) [Magma G] (h : Equation1334 G) : Equation4461 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq20 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ ((((X0 ◇ X1) ◇ X4) ◇ X2) ◇ X4)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq12 eq20 -- forward demodulation 20,12
  have eq35 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X3 ◇ X4) ◇ (X0 ◇ (X3 ◇ X1)))) = X4 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq49 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X4 ◇ X1))) = X4 := superpose eq24 eq35 -- forward demodulation 35,24
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.1.1 in 12
  have eq55 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1))) = X2 := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.2.2.1 in 11
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.1 in 12
  have eq62 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq70 : sK1 ≠ ((sK2 ◇ sK2) ◇ sK1) := superpose eq62 eq10 -- backward demodulation 10,62
  have eq85 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq56 eq55 -- backward demodulation 55,56
  have eq87 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq54 eq57 -- forward demodulation 57,54
  have eq88 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ X0) := superpose eq85 eq87 -- forward demodulation 87,85
  have eq111 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq62 eq49 -- superposition 49,62, 62 into 49, unify on (0).2 in 62 and (0).1.2 in 49
  have eq252 (X0 : G) : sK1 ≠ ((X0 ◇ X0) ◇ sK1) := superpose eq88 eq70 -- superposition 70,88, 88 into 70, unify on (0).2 in 88 and (0).2.1 in 70
  subsumption eq252 eq111


@[equational_result]
theorem Equation1334_implies_Equation1761 (G : Type*) [Magma G] (h : Equation1334 G) : Equation1761 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ ((((X0 ◇ X1) ◇ X4) ◇ X2) ◇ X4)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq35 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X3 ◇ X4) ◇ (X0 ◇ (X3 ◇ X1)))) = X4 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq49 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X4 ◇ X1))) = X4 := superpose eq24 eq35 -- forward demodulation 35,24
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.1.1 in 12
  have eq55 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1))) = X2 := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.2.2.1 in 11
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq62 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq84 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK0))) := superpose eq54 eq10 -- backward demodulation 10,54
  have eq85 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq56 eq55 -- backward demodulation 55,56
  have eq111 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq62 eq85 -- superposition 85,62, 62 into 85, unify on (0).2 in 62 and (0).1.2 in 85
  have eq115 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK1))) := superpose eq111 eq84 -- backward demodulation 84,111
  have eq157 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq49 eq19 -- superposition 19,49, 49 into 19, unify on (0).2 in 49 and (0).1.1 in 19
  have eq196 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK1))) := superpose eq157 eq115 -- backward demodulation 115,157
  have eq197 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := superpose eq111 eq196 -- forward demodulation 196,111
  subsumption eq197 eq62


@[equational_result]
theorem Equation1334_implies_Equation3703 (G : Type*) [Magma G] (h : Equation1334 G) : Equation3703 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.1.1 in 12
  have eq55 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1))) = X2 := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.2.2.1 in 11
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.1 in 12
  have eq62 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq84 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq56 eq55 -- backward demodulation 55,56
  have eq86 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq54 eq57 -- forward demodulation 57,54
  have eq87 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq84 eq86 -- forward demodulation 86,84
  have eq133 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq62 eq84 -- superposition 84,62, 62 into 84, unify on (0).2 in 62 and (0).1.2 in 84
  have eq141 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := superpose eq133 eq10 -- backward demodulation 10,133
  subsumption eq141 eq87


@[equational_result]
theorem Equation1334_implies_Equation2710 (G : Type*) [Magma G] (h : Equation1334 G) : Equation2710 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X1) ◇ X3)) = (X4 ◇ (X2 ◇ (((X4 ◇ X5) ◇ X0) ◇ X5))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq20 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ ((((X0 ◇ X1) ◇ X4) ◇ X2) ◇ X4)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq12 eq20 -- forward demodulation 20,12
  have eq35 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X3 ◇ X4) ◇ (X0 ◇ (X3 ◇ X1)))) = X4 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq49 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X4 ◇ X1))) = X4 := superpose eq24 eq35 -- forward demodulation 35,24
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq64 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) = (X2 ◇ X0) := superpose eq50 eq13 -- backward demodulation 13,50
  have eq65 (X0 X1 X2 X4 X5 : G) : (X4 ◇ (X2 ◇ (((X4 ◇ X5) ◇ X0) ◇ X5))) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq50 eq14 -- backward demodulation 14,50
  have eq70 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq50 eq64 -- forward demodulation 64,50
  have eq71 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = (X4 ◇ (X2 ◇ (X0 ◇ X4))) := superpose eq50 eq65 -- forward demodulation 65,50
  have eq72 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq70 eq71 -- forward demodulation 71,70
  have eq73 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq72 eq10 -- backward demodulation 10,72
  have eq122 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq49 eq56 -- superposition 56,49, 49 into 56, unify on (0).2 in 49 and (0).1 in 56
  have eq503 : sK0 ≠ sK0 := superpose eq122 eq73 -- superposition 73,122, 122 into 73, unify on (0).2 in 122 and (0).2 in 73
  subsumption eq503 rfl


@[equational_result]
theorem Equation1334_implies_Equation504 (G : Type*) [Magma G] (h : Equation1334 G) : Equation504 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq62 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq64 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) = (X2 ◇ X0) := superpose eq50 eq13 -- backward demodulation 13,50
  have eq70 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq50 eq64 -- forward demodulation 64,50
  have eq71 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq70 eq10 -- backward demodulation 10,70
  subsumption eq71 eq62


@[equational_result]
theorem Equation1334_implies_Equation833 (G : Type*) [Magma G] (h : Equation1334 G) : Equation833 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X1) ◇ X3)) = (X4 ◇ (X2 ◇ (((X4 ◇ X5) ◇ X0) ◇ X5))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.1.1 in 12
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq64 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) = (X2 ◇ X0) := superpose eq50 eq13 -- backward demodulation 13,50
  have eq65 (X0 X1 X2 X4 X5 : G) : (X4 ◇ (X2 ◇ (((X4 ◇ X5) ◇ X0) ◇ X5))) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq50 eq14 -- backward demodulation 14,50
  have eq70 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq50 eq64 -- forward demodulation 64,50
  have eq71 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = (X4 ◇ (X2 ◇ (X0 ◇ X4))) := superpose eq50 eq65 -- forward demodulation 65,50
  have eq72 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq70 eq71 -- forward demodulation 71,70
  have eq84 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := superpose eq54 eq10 -- backward demodulation 10,54
  have eq85 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq72 eq84 -- forward demodulation 84,72
  have eq132 : sK0 ≠ sK0 := superpose eq56 eq85 -- superposition 85,56, 56 into 85, unify on (0).2 in 56 and (0).2 in 85
  subsumption eq132 rfl


@[equational_result]
theorem Equation1334_implies_Equation3404 (G : Type*) [Magma G] (h : Equation1334 G) : Equation3404 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ ((((X0 ◇ X1) ◇ X4) ◇ X2) ◇ X4)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq35 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X3 ◇ X4) ◇ (X0 ◇ (X3 ◇ X1)))) = X4 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq49 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X4 ◇ X1))) = X4 := superpose eq24 eq35 -- forward demodulation 35,24
  have eq50 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq55 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1))) = X2 := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.2.2.1 in 11
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq62 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq64 (X0 X2 X3 X4 : G) : (X2 ◇ X0) = (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq50 eq13 -- backward demodulation 13,50
  have eq70 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq50 eq64 -- forward demodulation 64,50
  have eq84 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq56 eq55 -- backward demodulation 55,56
  have eq124 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq49 eq19 -- superposition 19,49, 49 into 19, unify on (0).2 in 49 and (0).1.1 in 19
  have eq133 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq62 eq84 -- superposition 84,62, 62 into 84, unify on (0).2 in 62 and (0).1.2 in 84
  have eq141 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := superpose eq133 eq10 -- backward demodulation 10,133
  have eq142 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := superpose eq124 eq141 -- forward demodulation 141,124
  subsumption eq142 eq70


@[equational_result]
theorem Equation1334_implies_Equation4364 (G : Type*) [Magma G] (h : Equation1334 G) : Equation4364 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ ((((X0 ◇ X1) ◇ X4) ◇ X2) ◇ X4)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq35 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X3 ◇ X4) ◇ (X0 ◇ (X3 ◇ X1)))) = X4 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq49 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X4 ◇ X1))) = X4 := superpose eq24 eq35 -- forward demodulation 35,24
  have eq50 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq55 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1))) = X2 := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.2.2.1 in 11
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq62 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq84 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq56 eq55 -- backward demodulation 55,56
  have eq124 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq49 eq19 -- superposition 19,49, 49 into 19, unify on (0).2 in 49 and (0).1.1 in 19
  have eq133 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq62 eq84 -- superposition 84,62, 62 into 84, unify on (0).2 in 62 and (0).1.2 in 84
  have eq141 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := superpose eq133 eq10 -- backward demodulation 10,133
  subsumption eq141 eq124


@[equational_result]
theorem Equation1334_implies_Equation906 (G : Type*) [Magma G] (h : Equation1334 G) : Equation906 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X1) ◇ X3)) = (X4 ◇ (X2 ◇ (((X4 ◇ X5) ◇ X0) ◇ X5))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq58 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.1.1 in 12
  have eq62 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq64 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) = (X2 ◇ X0) := superpose eq50 eq13 -- backward demodulation 13,50
  have eq65 (X0 X1 X2 X4 X5 : G) : (X4 ◇ (X2 ◇ (((X4 ◇ X5) ◇ X0) ◇ X5))) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq50 eq14 -- backward demodulation 14,50
  have eq70 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq50 eq64 -- forward demodulation 64,50
  have eq71 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = (X4 ◇ (X2 ◇ (X0 ◇ X4))) := superpose eq50 eq65 -- forward demodulation 65,50
  have eq72 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq70 eq71 -- forward demodulation 71,70
  have eq86 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))) := superpose eq58 eq10 -- backward demodulation 10,58
  have eq87 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq72 eq86 -- forward demodulation 86,72
  subsumption eq87 eq62


@[equational_result]
theorem Equation1334_implies_Equation1368 (G : Type*) [Magma G] (h : Equation1334 G) : Equation1368 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK1) ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.1.1 in 12
  have eq55 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1))) = X2 := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.2.2.1 in 11
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq62 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq64 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) = (X2 ◇ X0) := superpose eq50 eq13 -- backward demodulation 13,50
  have eq70 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq50 eq64 -- forward demodulation 64,50
  have eq84 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) := superpose eq54 eq10 -- backward demodulation 10,54
  have eq85 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ sK0))) := superpose eq54 eq84 -- forward demodulation 84,54
  have eq86 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := superpose eq54 eq85 -- forward demodulation 85,54
  have eq87 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq56 eq55 -- backward demodulation 55,56
  have eq113 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq62 eq87 -- superposition 87,62, 62 into 87, unify on (0).2 in 62 and (0).1.2 in 87
  have eq117 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := superpose eq113 eq86 -- backward demodulation 86,113
  have eq118 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq70 eq117 -- forward demodulation 117,70
  subsumption eq118 eq62


@[equational_result]
theorem Equation1334_implies_Equation655 (G : Type*) [Magma G] (h : Equation1334 G) : Equation655 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq24 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq31 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq59 : sK0 ≠ sK0 := superpose eq31 eq24 -- superposition 24,31, 31 into 24, unify on (0).2 in 31 and (0).2 in 24
  subsumption eq59 rfl


@[equational_result]
theorem Equation1334_implies_Equation2592 (G : Type*) [Magma G] (h : Equation1334 G) : Equation2592 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK1) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq24 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq31 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq55 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq19 eq31 -- superposition 31,19, 19 into 31, unify on (0).2 in 19 and (0).1 in 31
  have eq163 : sK0 ≠ sK0 := superpose eq55 eq24 -- superposition 24,55, 55 into 24, unify on (0).2 in 55 and (0).2 in 24
  subsumption eq163 rfl


@[equational_result]
theorem Equation1334_implies_Equation4120 (G : Type*) [Magma G] (h : Equation1334 G) : Equation4120 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.1.1 in 12
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq64 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) = (X2 ◇ X0) := superpose eq50 eq13 -- backward demodulation 13,50
  have eq70 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq50 eq64 -- forward demodulation 64,50
  have eq84 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq54 eq10 -- backward demodulation 10,54
  have eq87 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq56 eq84 -- backward demodulation 84,56
  have eq139 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq56 eq70 -- superposition 70,56, 56 into 70, unify on (0).2 in 56 and (0).2.2 in 70
  have eq765 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq139 eq87 -- superposition 87,139, 139 into 87, unify on (0).2 in 139 and (0).2 in 87
  subsumption eq765 rfl


@[equational_result]
theorem Equation1334_implies_Equation2789 (G : Type*) [Magma G] (h : Equation1334 G) : Equation2789 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK1 ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X1) ◇ X3)) = (X4 ◇ (X2 ◇ (((X4 ◇ X5) ◇ X0) ◇ X5))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq64 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) = (X2 ◇ X0) := superpose eq50 eq13 -- backward demodulation 13,50
  have eq65 (X0 X1 X2 X4 X5 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = (X4 ◇ (X2 ◇ (((X4 ◇ X5) ◇ X0) ◇ X5))) := superpose eq50 eq14 -- backward demodulation 14,50
  have eq70 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq50 eq64 -- forward demodulation 64,50
  have eq71 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = (X4 ◇ (X2 ◇ (X0 ◇ X4))) := superpose eq50 eq65 -- forward demodulation 65,50
  have eq72 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = (X2 ◇ X0) := superpose eq70 eq71 -- forward demodulation 71,70
  have eq73 : sK0 ≠ ((sK2 ◇ sK0) ◇ sK2) := superpose eq72 eq10 -- backward demodulation 10,72
  subsumption eq73 eq19


@[equational_result]
theorem Equation1334_implies_Equation910 (G : Type*) [Magma G] (h : Equation1334 G) : Equation910 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X1) ◇ X3)) = (X4 ◇ (X2 ◇ (((X4 ◇ X5) ◇ X0) ◇ X5))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq62 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq64 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) = (X2 ◇ X0) := superpose eq50 eq13 -- backward demodulation 13,50
  have eq65 (X0 X1 X2 X4 X5 : G) : (X4 ◇ (X2 ◇ (((X4 ◇ X5) ◇ X0) ◇ X5))) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq50 eq14 -- backward demodulation 14,50
  have eq70 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq50 eq64 -- forward demodulation 64,50
  have eq71 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = (X4 ◇ (X2 ◇ (X0 ◇ X4))) := superpose eq50 eq65 -- forward demodulation 65,50
  have eq72 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq70 eq71 -- forward demodulation 71,70
  have eq73 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq72 eq10 -- backward demodulation 10,72
  subsumption eq73 eq62


@[equational_result]
theorem Equation895_implies_Equation2402 (G : Type*) [Magma G] (h : Equation895 G) : Equation2402 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.2 in 12
  have eq33 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2.2 in 11
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq36 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1 in 12
  have eq58 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X2) = X3 := superpose eq17 eq34 -- superposition 34,17, 17 into 34, unify on (0).2 in 17 and (0).1.1.2.1 in 34
  have eq73 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) = X3 := superpose eq17 eq34 -- superposition 34,17, 17 into 34, unify on (0).2 in 17 and (0).1 in 34
  have eq77 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) := superpose eq34 eq9 -- superposition 9,34, 34 into 9, unify on (0).2 in 34 and (0).1.2 in 9
  have eq84 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X4) ◇ ((X5 ◇ X3) ◇ X4))) = (X2 ◇ (X5 ◇ X0)) := superpose eq34 eq12 -- superposition 12,34, 34 into 12, unify on (0).2 in 34 and (0).1.2.1 in 12
  have eq87 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2) = X3 := superpose eq17 eq58 -- forward demodulation 58,17
  have eq88 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X3 := superpose eq36 eq87 -- forward demodulation 87,36
  have eq92 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq77 eq26 -- backward demodulation 26,77
  have eq93 (X0 X2 X4 : G) : (X4 ◇ (X0 ◇ (X4 ◇ X2))) = (X2 ◇ X0) := superpose eq77 eq33 -- backward demodulation 33,77
  have eq101 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq92 eq73 -- backward demodulation 73,92
  have eq116 (X0 X1 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X5) := superpose eq92 eq84 -- forward demodulation 84,92
  have eq134 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3)) = X2 := superpose eq36 eq12 -- superposition 12,36, 36 into 12, unify on (0).2 in 36 and (0).1.2.1.2.2 in 12
  have eq190 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X1 ◇ X0) := superpose eq9 eq88 -- superposition 88,9, 9 into 88, unify on (0).2 in 9 and (0).1.1 in 88
  have eq235 (X0 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = ((X0 ◇ X2) ◇ X5) := superpose eq190 eq116 -- backward demodulation 116,190
  have eq258 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X3 ◇ X2))) = X2 := superpose eq235 eq134 -- backward demodulation 134,235
  have eq286 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X3 ◇ X2) ◇ (X3 ◇ (X1 ◇ X0))))) = X2 := superpose eq235 eq258 -- forward demodulation 258,235
  have eq287 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)))) = X2 := superpose eq235 eq286 -- forward demodulation 286,235
  have eq288 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq88 eq287 -- forward demodulation 287,88
  have eq289 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq93 eq288 -- forward demodulation 288,93
  have eq291 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq289 eq10 -- backward demodulation 10,289
  subsumption eq291 eq101


@[equational_result]
theorem Equation895_implies_Equation2936 (G : Type*) [Magma G] (h : Equation895 G) : Equation2936 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.2 in 12
  have eq28 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2.2 in 11
  have eq29 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq38 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.2 in 9
  have eq58 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X2) = X3 := superpose eq17 eq29 -- superposition 29,17, 17 into 29, unify on (0).2 in 17 and (0).1.1.2.1 in 29
  have eq77 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) := superpose eq29 eq9 -- superposition 9,29, 29 into 9, unify on (0).2 in 29 and (0).1.2 in 9
  have eq84 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X4) ◇ ((X5 ◇ X3) ◇ X4))) = (X2 ◇ (X5 ◇ X0)) := superpose eq29 eq12 -- superposition 12,29, 29 into 12, unify on (0).2 in 29 and (0).1.2.1 in 12
  have eq87 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2) = X3 := superpose eq17 eq58 -- forward demodulation 58,17
  have eq88 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X3 := superpose eq38 eq87 -- forward demodulation 87,38
  have eq92 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq77 eq26 -- backward demodulation 26,77
  have eq93 (X0 X2 X4 : G) : (X4 ◇ (X0 ◇ (X4 ◇ X2))) = (X2 ◇ X0) := superpose eq77 eq28 -- backward demodulation 28,77
  have eq116 (X0 X1 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X5) := superpose eq92 eq84 -- forward demodulation 84,92
  have eq134 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3)) = X2 := superpose eq38 eq12 -- superposition 12,38, 38 into 12, unify on (0).2 in 38 and (0).1.2.1.2.2 in 12
  have eq190 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq9 eq88 -- superposition 88,9, 9 into 88, unify on (0).2 in 9 and (0).1.1 in 88
  have eq235 (X0 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = ((X0 ◇ X2) ◇ X5) := superpose eq190 eq116 -- backward demodulation 116,190
  have eq258 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X3 ◇ X2))) = X2 := superpose eq235 eq134 -- backward demodulation 134,235
  have eq271 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq235 eq10 -- backward demodulation 10,235
  have eq287 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X3 ◇ X2) ◇ (X3 ◇ (X1 ◇ X0))))) = X2 := superpose eq235 eq258 -- forward demodulation 258,235
  have eq288 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)))) = X2 := superpose eq235 eq287 -- forward demodulation 287,235
  have eq289 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq88 eq288 -- forward demodulation 288,88
  have eq290 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq93 eq289 -- forward demodulation 289,93
  have eq335 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK0) := superpose eq235 eq271 -- forward demodulation 271,235
  have eq336 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) := superpose eq235 eq335 -- forward demodulation 335,235
  have eq337 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq290 eq336 -- forward demodulation 336,290
  subsumption eq337 eq88


@[equational_result]
theorem Equation895_implies_Equation978 (G : Type*) [Magma G] (h : Equation895 G) : Equation978 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.2 in 12
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq36 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1 in 12
  have eq73 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) = X3 := superpose eq17 eq34 -- superposition 34,17, 17 into 34, unify on (0).2 in 17 and (0).1 in 34
  have eq77 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) := superpose eq34 eq9 -- superposition 9,34, 34 into 9, unify on (0).2 in 34 and (0).1.2 in 9
  have eq92 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq77 eq26 -- backward demodulation 26,77
  have eq101 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq92 eq73 -- backward demodulation 73,92
  have eq105 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq101 eq10 -- backward demodulation 10,101
  subsumption eq105 eq36


@[equational_result]
theorem Equation895_implies_Equation1993 (G : Type*) [Magma G] (h : Equation895 G) : Equation1993 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq20 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq22 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1.2.2 in 11
  have eq71 : sK0 ≠ sK0 := superpose eq22 eq20 -- superposition 20,22, 22 into 20, unify on (0).2 in 22 and (0).2 in 20
  subsumption eq71 rfl


@[equational_result]
theorem Equation895_implies_Equation775 (G : Type*) [Magma G] (h : Equation895 G) : Equation775 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK2 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.2 in 12
  have eq33 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2.2 in 11
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq36 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1 in 12
  have eq58 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X2) = X3 := superpose eq17 eq34 -- superposition 34,17, 17 into 34, unify on (0).2 in 17 and (0).1.1.2.1 in 34
  have eq73 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) = X3 := superpose eq17 eq34 -- superposition 34,17, 17 into 34, unify on (0).2 in 17 and (0).1 in 34
  have eq77 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) := superpose eq34 eq9 -- superposition 9,34, 34 into 9, unify on (0).2 in 34 and (0).1.2 in 9
  have eq84 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X4) ◇ ((X5 ◇ X3) ◇ X4))) = (X2 ◇ (X5 ◇ X0)) := superpose eq34 eq12 -- superposition 12,34, 34 into 12, unify on (0).2 in 34 and (0).1.2.1 in 12
  have eq87 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2) = X3 := superpose eq17 eq58 -- forward demodulation 58,17
  have eq88 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X3 := superpose eq36 eq87 -- forward demodulation 87,36
  have eq92 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq77 eq26 -- backward demodulation 26,77
  have eq93 (X0 X2 X4 : G) : (X2 ◇ X0) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq77 eq33 -- backward demodulation 33,77
  have eq101 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq92 eq73 -- backward demodulation 73,92
  have eq116 (X0 X1 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X5) := superpose eq92 eq84 -- forward demodulation 84,92
  have eq190 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X1 ◇ X0) := superpose eq9 eq88 -- superposition 88,9, 9 into 88, unify on (0).2 in 9 and (0).1.1 in 88
  have eq235 (X0 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = ((X0 ◇ X2) ◇ X5) := superpose eq190 eq116 -- backward demodulation 116,190
  have eq261 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ (X2 ◇ (X0 ◇ X4))) = X4 := superpose eq235 eq92 -- backward demodulation 92,235
  have eq271 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := superpose eq235 eq10 -- backward demodulation 10,235
  have eq403 (X0 X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq101 eq93 -- superposition 93,101, 101 into 93, unify on (0).2 in 101 and (0).2 in 93
  have eq412 (X0 X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq235 eq403 -- forward demodulation 403,235
  have eq413 (X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ X1) := superpose eq36 eq412 -- forward demodulation 412,36
  have eq472 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := superpose eq261 eq88 -- superposition 88,261, 261 into 88, unify on (0).2 in 261 and (0).1.1 in 88
  have eq504 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2))) := superpose eq472 eq271 -- backward demodulation 271,472
  have eq505 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := superpose eq413 eq504 -- forward demodulation 504,413
  have eq506 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq36 eq505 -- forward demodulation 505,36
  subsumption eq506 eq36


@[equational_result]
theorem Equation895_implies_Equation2998 (G : Type*) [Magma G] (h : Equation895 G) : Equation2998 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq36 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1 in 12
  have eq49 : sK0 ≠ ((sK2 ◇ sK2) ◇ sK0) := superpose eq36 eq10 -- backward demodulation 10,36
  have eq57 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq17 eq36 -- superposition 36,17, 17 into 36, unify on (0).2 in 17 and (0).1.2 in 36
  have eq322 : sK0 ≠ sK0 := superpose eq57 eq49 -- superposition 49,57, 57 into 49, unify on (0).2 in 57 and (0).2 in 49
  subsumption eq322 rfl


@[equational_result]
theorem Equation895_implies_Equation778 (G : Type*) [Magma G] (h : Equation895 G) : Equation778 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK2 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.2 in 12
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq36 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1 in 12
  have eq58 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X2) = X3 := superpose eq17 eq34 -- superposition 34,17, 17 into 34, unify on (0).2 in 17 and (0).1.1.2.1 in 34
  have eq77 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) := superpose eq34 eq9 -- superposition 9,34, 34 into 9, unify on (0).2 in 34 and (0).1.2 in 9
  have eq84 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X4) ◇ ((X5 ◇ X3) ◇ X4))) = (X2 ◇ (X5 ◇ X0)) := superpose eq34 eq12 -- superposition 12,34, 34 into 12, unify on (0).2 in 34 and (0).1.2.1 in 12
  have eq87 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2) = X3 := superpose eq17 eq58 -- forward demodulation 58,17
  have eq88 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X3 := superpose eq36 eq87 -- forward demodulation 87,36
  have eq92 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq77 eq26 -- backward demodulation 26,77
  have eq116 (X0 X1 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X5) := superpose eq92 eq84 -- forward demodulation 84,92
  have eq132 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X1)))) = X0 := superpose eq36 eq11 -- superposition 11,36, 36 into 11, unify on (0).2 in 36 and (0).1.2.2.2.2 in 11
  have eq190 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X1 ◇ X0) := superpose eq9 eq88 -- superposition 88,9, 9 into 88, unify on (0).2 in 9 and (0).1.1 in 88
  have eq235 (X0 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = ((X0 ◇ X2) ◇ X5) := superpose eq190 eq116 -- backward demodulation 116,190
  have eq259 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X3))))) = X0 := superpose eq235 eq132 -- backward demodulation 132,235
  have eq271 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := superpose eq235 eq10 -- backward demodulation 10,235
  have eq292 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X3) ◇ X1))))) = X0 := superpose eq235 eq259 -- forward demodulation 259,235
  have eq293 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := superpose eq88 eq292 -- forward demodulation 292,88
  subsumption eq271 eq293


@[equational_result]
theorem Equation895_implies_Equation765 (G : Type*) [Magma G] (h : Equation895 G) : Equation765 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.2 in 12
  have eq33 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2.2 in 11
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq36 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1 in 12
  have eq58 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X2) = X3 := superpose eq17 eq34 -- superposition 34,17, 17 into 34, unify on (0).2 in 17 and (0).1.1.2.1 in 34
  have eq77 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) := superpose eq34 eq9 -- superposition 9,34, 34 into 9, unify on (0).2 in 34 and (0).1.2 in 9
  have eq84 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X4) ◇ ((X5 ◇ X3) ◇ X4))) = (X2 ◇ (X5 ◇ X0)) := superpose eq34 eq12 -- superposition 12,34, 34 into 12, unify on (0).2 in 34 and (0).1.2.1 in 12
  have eq87 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2) = X3 := superpose eq17 eq58 -- forward demodulation 58,17
  have eq88 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X3 := superpose eq36 eq87 -- forward demodulation 87,36
  have eq92 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq77 eq26 -- backward demodulation 26,77
  have eq93 (X0 X2 X4 : G) : (X4 ◇ (X0 ◇ (X4 ◇ X2))) = (X2 ◇ X0) := superpose eq77 eq33 -- backward demodulation 33,77
  have eq116 (X0 X1 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X5) := superpose eq92 eq84 -- forward demodulation 84,92
  have eq134 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3)) = X2 := superpose eq36 eq12 -- superposition 12,36, 36 into 12, unify on (0).2 in 36 and (0).1.2.1.2.2 in 12
  have eq190 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X1 ◇ X0) := superpose eq9 eq88 -- superposition 88,9, 9 into 88, unify on (0).2 in 9 and (0).1.1 in 88
  have eq235 (X0 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = ((X0 ◇ X2) ◇ X5) := superpose eq190 eq116 -- backward demodulation 116,190
  have eq258 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X3 ◇ X2))) = X2 := superpose eq235 eq134 -- backward demodulation 134,235
  have eq271 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := superpose eq235 eq10 -- backward demodulation 10,235
  have eq287 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X3 ◇ X2) ◇ (X3 ◇ (X1 ◇ X0))))) = X2 := superpose eq235 eq258 -- forward demodulation 258,235
  have eq288 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)))) = X2 := superpose eq235 eq287 -- forward demodulation 287,235
  have eq289 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq88 eq288 -- forward demodulation 288,88
  have eq290 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq93 eq289 -- forward demodulation 289,93
  have eq335 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq290 eq271 -- forward demodulation 271,290
  subsumption eq335 eq36


@[equational_result]
theorem Equation895_implies_Equation2808 (G : Type*) [Magma G] (h : Equation895 G) : Equation2808 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK2 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.2 in 12
  have eq33 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2.2 in 11
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq36 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1 in 12
  have eq58 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X2) = X3 := superpose eq17 eq34 -- superposition 34,17, 17 into 34, unify on (0).2 in 17 and (0).1.1.2.1 in 34
  have eq73 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) = X3 := superpose eq17 eq34 -- superposition 34,17, 17 into 34, unify on (0).2 in 17 and (0).1 in 34
  have eq77 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) := superpose eq34 eq9 -- superposition 9,34, 34 into 9, unify on (0).2 in 34 and (0).1.2 in 9
  have eq84 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X4) ◇ ((X5 ◇ X3) ◇ X4))) = (X2 ◇ (X5 ◇ X0)) := superpose eq34 eq12 -- superposition 12,34, 34 into 12, unify on (0).2 in 34 and (0).1.2.1 in 12
  have eq87 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2) = X3 := superpose eq17 eq58 -- forward demodulation 58,17
  have eq88 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X3 := superpose eq36 eq87 -- forward demodulation 87,36
  have eq92 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq77 eq26 -- backward demodulation 26,77
  have eq93 (X0 X2 X4 : G) : (X4 ◇ (X0 ◇ (X4 ◇ X2))) = (X2 ◇ X0) := superpose eq77 eq33 -- backward demodulation 33,77
  have eq101 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq92 eq73 -- backward demodulation 73,92
  have eq116 (X0 X1 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X5) := superpose eq92 eq84 -- forward demodulation 84,92
  have eq134 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3)) = X2 := superpose eq36 eq12 -- superposition 12,36, 36 into 12, unify on (0).2 in 36 and (0).1.2.1.2.2 in 12
  have eq190 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X1 ◇ X0) := superpose eq9 eq88 -- superposition 88,9, 9 into 88, unify on (0).2 in 9 and (0).1.1 in 88
  have eq235 (X0 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = ((X0 ◇ X2) ◇ X5) := superpose eq190 eq116 -- backward demodulation 116,190
  have eq258 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X3 ◇ X2))) = X2 := superpose eq235 eq134 -- backward demodulation 134,235
  have eq271 : sK0 ≠ ((sK2 ◇ ((sK2 ◇ sK1) ◇ sK1)) ◇ sK0) := superpose eq235 eq10 -- backward demodulation 10,235
  have eq287 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X3 ◇ X2) ◇ (X3 ◇ (X1 ◇ X0))))) = X2 := superpose eq235 eq258 -- forward demodulation 258,235
  have eq288 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)))) = X2 := superpose eq235 eq287 -- forward demodulation 287,235
  have eq289 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq88 eq288 -- forward demodulation 288,88
  have eq290 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq93 eq289 -- forward demodulation 289,93
  have eq335 : sK0 ≠ ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ sK0) := superpose eq235 eq271 -- forward demodulation 271,235
  have eq336 : sK0 ≠ ((sK2 ◇ sK2) ◇ sK0) := superpose eq290 eq335 -- forward demodulation 335,290
  subsumption eq336 eq101


@[equational_result]
theorem Equation895_implies_Equation2088 (G : Type*) [Magma G] (h : Equation895 G) : Equation2088 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.2 in 12
  have eq28 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2.2 in 11
  have eq29 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq38 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.2 in 9
  have eq58 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X2) = X3 := superpose eq17 eq29 -- superposition 29,17, 17 into 29, unify on (0).2 in 17 and (0).1.1.2.1 in 29
  have eq83 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) := superpose eq29 eq9 -- superposition 9,29, 29 into 9, unify on (0).2 in 29 and (0).1.2 in 9
  have eq84 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X4) ◇ ((X5 ◇ X3) ◇ X4))) = (X2 ◇ (X5 ◇ X0)) := superpose eq29 eq12 -- superposition 12,29, 29 into 12, unify on (0).2 in 29 and (0).1.2.1 in 12
  have eq87 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2) = X3 := superpose eq17 eq58 -- forward demodulation 58,17
  have eq88 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X3 := superpose eq38 eq87 -- forward demodulation 87,38
  have eq92 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq83 eq26 -- backward demodulation 26,83
  have eq93 (X0 X2 X4 : G) : (X4 ◇ (X0 ◇ (X4 ◇ X2))) = (X2 ◇ X0) := superpose eq83 eq28 -- backward demodulation 28,83
  have eq114 (X0 X1 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X5) := superpose eq92 eq84 -- forward demodulation 84,92
  have eq127 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := superpose eq38 eq11 -- superposition 11,38, 38 into 11, unify on (0).2 in 38 and (0).1.2.2 in 11
  have eq132 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3)) = X2 := superpose eq38 eq12 -- superposition 12,38, 38 into 12, unify on (0).2 in 38 and (0).1.2.1.2.2 in 12
  have eq188 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq9 eq88 -- superposition 88,9, 9 into 88, unify on (0).2 in 9 and (0).1.1 in 88
  have eq233 (X0 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = ((X0 ◇ X2) ◇ X5) := superpose eq188 eq114 -- backward demodulation 114,188
  have eq256 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X3 ◇ X2))) = X2 := superpose eq233 eq132 -- backward demodulation 132,233
  have eq269 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := superpose eq233 eq10 -- backward demodulation 10,233
  have eq285 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X3 ◇ X2) ◇ (X3 ◇ (X1 ◇ X0))))) = X2 := superpose eq233 eq256 -- forward demodulation 256,233
  have eq286 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)))) = X2 := superpose eq233 eq285 -- forward demodulation 285,233
  have eq287 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq88 eq286 -- forward demodulation 286,88
  have eq288 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq93 eq287 -- forward demodulation 287,93
  have eq289 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq288 eq127 -- backward demodulation 127,288
  subsumption eq269 eq289


@[equational_result]
theorem Equation895_implies_Equation2850 (G : Type*) [Magma G] (h : Equation895 G) : Equation2850 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq20 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq22 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1.2.2 in 11
  have eq52 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2.2 in 11
  have eq53 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq56 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq22 eq22 -- superposition 22,22, 22 into 22, unify on (0).2 in 22 and (0).1.2 in 22
  have eq69 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3)) = X2 := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.2.1.2.2 in 12
  have eq93 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq22 eq53 -- superposition 53,22, 22 into 53, unify on (0).2 in 22 and (0).1.1 in 53
  have eq108 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X4) ◇ ((X5 ◇ X3) ◇ X4))) = (X2 ◇ (X5 ◇ X0)) := superpose eq53 eq12 -- superposition 12,53, 53 into 12, unify on (0).2 in 53 and (0).1.2.1 in 12
  have eq122 (X0 X2 X4 : G) : (X2 ◇ X0) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq93 eq52 -- backward demodulation 52,93
  have eq142 (X0 X1 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X5) := superpose eq93 eq108 -- forward demodulation 108,93
  have eq148 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X1 ◇ X0) := superpose eq9 eq56 -- superposition 56,9, 9 into 56, unify on (0).2 in 9 and (0).1.1 in 56
  have eq197 (X0 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = ((X0 ◇ X2) ◇ X5) := superpose eq148 eq142 -- backward demodulation 142,148
  have eq222 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X3 ◇ X2))) = X2 := superpose eq197 eq69 -- backward demodulation 69,197
  have eq232 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X3 ◇ X2) ◇ (X3 ◇ (X1 ◇ X0))))) = X2 := superpose eq197 eq222 -- forward demodulation 222,197
  have eq233 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)))) = X2 := superpose eq197 eq232 -- forward demodulation 232,197
  have eq234 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq56 eq233 -- forward demodulation 233,56
  have eq235 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq122 eq234 -- forward demodulation 234,122
  have eq348 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq197 eq20 -- superposition 20,197, 197 into 20, unify on (0).2 in 197 and (0).2 in 20
  subsumption eq348 eq235


@[equational_result]
theorem Equation895_implies_Equation2241 (G : Type*) [Magma G] (h : Equation895 G) : Equation2241 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq28 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2.2 in 11
  have eq29 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq38 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.2 in 9
  have eq58 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X2) = X3 := superpose eq17 eq29 -- superposition 29,17, 17 into 29, unify on (0).2 in 17 and (0).1.1.2.1 in 29
  have eq77 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) := superpose eq29 eq9 -- superposition 9,29, 29 into 9, unify on (0).2 in 29 and (0).1.2 in 9
  have eq87 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2) = X3 := superpose eq17 eq58 -- forward demodulation 58,17
  have eq88 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X3 := superpose eq38 eq87 -- forward demodulation 87,38
  have eq93 (X0 X2 X4 : G) : (X4 ◇ (X0 ◇ (X4 ◇ X2))) = (X2 ◇ X0) := superpose eq77 eq28 -- backward demodulation 28,77
  have eq108 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq93 eq10 -- backward demodulation 10,93
  subsumption eq108 eq88


@[equational_result]
theorem Equation895_implies_Equation1876 (G : Type*) [Magma G] (h : Equation895 G) : Equation1876 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.2 in 12
  have eq33 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2.2 in 11
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq36 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1 in 12
  have eq58 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X2) = X3 := superpose eq17 eq34 -- superposition 34,17, 17 into 34, unify on (0).2 in 17 and (0).1.1.2.1 in 34
  have eq73 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) = X3 := superpose eq17 eq34 -- superposition 34,17, 17 into 34, unify on (0).2 in 17 and (0).1 in 34
  have eq77 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) := superpose eq34 eq9 -- superposition 9,34, 34 into 9, unify on (0).2 in 34 and (0).1.2 in 9
  have eq84 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X4) ◇ ((X5 ◇ X3) ◇ X4))) = (X2 ◇ (X5 ◇ X0)) := superpose eq34 eq12 -- superposition 12,34, 34 into 12, unify on (0).2 in 34 and (0).1.2.1 in 12
  have eq87 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2) = X3 := superpose eq17 eq58 -- forward demodulation 58,17
  have eq88 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X3 := superpose eq36 eq87 -- forward demodulation 87,36
  have eq92 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq77 eq26 -- backward demodulation 26,77
  have eq93 (X0 X2 X4 : G) : (X4 ◇ (X0 ◇ (X4 ◇ X2))) = (X2 ◇ X0) := superpose eq77 eq33 -- backward demodulation 33,77
  have eq101 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq92 eq73 -- backward demodulation 73,92
  have eq116 (X0 X1 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X5) := superpose eq92 eq84 -- forward demodulation 84,92
  have eq129 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := superpose eq36 eq11 -- superposition 11,36, 36 into 11, unify on (0).2 in 36 and (0).1.2.2 in 11
  have eq134 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3)) = X2 := superpose eq36 eq12 -- superposition 12,36, 36 into 12, unify on (0).2 in 36 and (0).1.2.1.2.2 in 12
  have eq190 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X1 ◇ X0) := superpose eq9 eq88 -- superposition 88,9, 9 into 88, unify on (0).2 in 9 and (0).1.1 in 88
  have eq235 (X0 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = ((X0 ◇ X2) ◇ X5) := superpose eq190 eq116 -- backward demodulation 116,190
  have eq258 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X3 ◇ X2))) = X2 := superpose eq235 eq134 -- backward demodulation 134,235
  have eq286 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X3 ◇ X2) ◇ (X3 ◇ (X1 ◇ X0))))) = X2 := superpose eq235 eq258 -- forward demodulation 258,235
  have eq287 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)))) = X2 := superpose eq235 eq286 -- forward demodulation 286,235
  have eq288 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq88 eq287 -- forward demodulation 287,88
  have eq289 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq93 eq288 -- forward demodulation 288,93
  have eq290 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq289 eq129 -- backward demodulation 129,289
  have eq401 (X0 X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq93 eq101 -- superposition 101,93, 93 into 101, unify on (0).2 in 93 and (0).1 in 101
  have eq410 (X0 X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq235 eq401 -- forward demodulation 401,235
  have eq411 (X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ X1) := superpose eq36 eq410 -- forward demodulation 410,36
  have eq412 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := superpose eq411 eq10 -- backward demodulation 10,411
  subsumption eq412 eq290


@[equational_result]
theorem Equation895_implies_Equation1571 (G : Type*) [Magma G] (h : Equation895 G) : Equation1571 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.2 in 12
  have eq28 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2.2 in 11
  have eq29 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq38 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.2 in 9
  have eq58 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X2) = X3 := superpose eq17 eq29 -- superposition 29,17, 17 into 29, unify on (0).2 in 17 and (0).1.1.2.1 in 29
  have eq73 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) = X3 := superpose eq17 eq29 -- superposition 29,17, 17 into 29, unify on (0).2 in 17 and (0).1 in 29
  have eq83 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) := superpose eq29 eq9 -- superposition 9,29, 29 into 9, unify on (0).2 in 29 and (0).1.2 in 9
  have eq84 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X4) ◇ ((X5 ◇ X3) ◇ X4))) = (X2 ◇ (X5 ◇ X0)) := superpose eq29 eq12 -- superposition 12,29, 29 into 12, unify on (0).2 in 29 and (0).1.2.1 in 12
  have eq87 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2) = X3 := superpose eq17 eq58 -- forward demodulation 58,17
  have eq88 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X3 := superpose eq38 eq87 -- forward demodulation 87,38
  have eq92 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq83 eq26 -- backward demodulation 26,83
  have eq93 (X0 X2 X4 : G) : (X4 ◇ (X0 ◇ (X4 ◇ X2))) = (X2 ◇ X0) := superpose eq83 eq28 -- backward demodulation 28,83
  have eq105 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq92 eq73 -- backward demodulation 73,92
  have eq114 (X0 X1 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X5) := superpose eq92 eq84 -- forward demodulation 84,92
  have eq188 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X1 ◇ X0) := superpose eq9 eq88 -- superposition 88,9, 9 into 88, unify on (0).2 in 9 and (0).1.1 in 88
  have eq233 (X0 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = ((X0 ◇ X2) ◇ X5) := superpose eq188 eq114 -- backward demodulation 114,188
  have eq259 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ (X2 ◇ (X0 ◇ X4))) = X4 := superpose eq233 eq92 -- backward demodulation 92,233
  have eq399 (X0 X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq93 eq105 -- superposition 105,93, 93 into 105, unify on (0).2 in 93 and (0).1 in 105
  have eq408 (X0 X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq233 eq399 -- forward demodulation 399,233
  have eq409 (X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ X1) := superpose eq38 eq408 -- forward demodulation 408,38
  have eq437 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := superpose eq259 eq88 -- superposition 88,259, 259 into 88, unify on (0).2 in 259 and (0).1.1 in 88
  have eq461 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK1))) := superpose eq437 eq10 -- backward demodulation 10,437
  have eq462 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := superpose eq409 eq461 -- forward demodulation 461,409
  subsumption eq462 eq38


@[equational_result]
theorem Equation895_implies_Equation2744 (G : Type*) [Magma G] (h : Equation895 G) : Equation2744 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.2 in 12
  have eq29 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq38 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.2 in 9
  have eq58 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X2) = X3 := superpose eq17 eq29 -- superposition 29,17, 17 into 29, unify on (0).2 in 17 and (0).1.1.2.1 in 29
  have eq73 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) = X3 := superpose eq17 eq29 -- superposition 29,17, 17 into 29, unify on (0).2 in 17 and (0).1 in 29
  have eq77 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) := superpose eq29 eq9 -- superposition 9,29, 29 into 9, unify on (0).2 in 29 and (0).1.2 in 9
  have eq87 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2) = X3 := superpose eq17 eq58 -- forward demodulation 58,17
  have eq88 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X3 := superpose eq38 eq87 -- forward demodulation 87,38
  have eq92 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq77 eq26 -- backward demodulation 26,77
  have eq101 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq92 eq73 -- backward demodulation 73,92
  have eq105 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq101 eq10 -- backward demodulation 10,101
  subsumption eq105 eq88


@[equational_result]
theorem Equation895_implies_Equation1455 (G : Type*) [Magma G] (h : Equation895 G) : Equation1455 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq20 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq24 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.2 in 9
  have eq48 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2.2 in 11
  have eq49 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq56 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq24 eq24 -- superposition 24,24, 24 into 24, unify on (0).2 in 24 and (0).1.2 in 24
  have eq69 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3)) = X2 := superpose eq24 eq12 -- superposition 12,24, 24 into 12, unify on (0).2 in 24 and (0).1.2.1.2.2 in 12
  have eq93 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq24 eq49 -- superposition 49,24, 24 into 49, unify on (0).2 in 24 and (0).1.1 in 49
  have eq108 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X4) ◇ ((X5 ◇ X3) ◇ X4))) = (X2 ◇ (X5 ◇ X0)) := superpose eq49 eq12 -- superposition 12,49, 49 into 12, unify on (0).2 in 49 and (0).1.2.1 in 12
  have eq122 (X0 X2 X4 : G) : (X2 ◇ X0) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq93 eq48 -- backward demodulation 48,93
  have eq142 (X0 X1 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X5) := superpose eq93 eq108 -- forward demodulation 108,93
  have eq148 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X1 ◇ X0) := superpose eq9 eq56 -- superposition 56,9, 9 into 56, unify on (0).2 in 9 and (0).1.1 in 56
  have eq197 (X0 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = ((X0 ◇ X2) ◇ X5) := superpose eq148 eq142 -- backward demodulation 142,148
  have eq222 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X3 ◇ X2))) = X2 := superpose eq197 eq69 -- backward demodulation 69,197
  have eq232 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X3 ◇ X2) ◇ (X3 ◇ (X1 ◇ X0))))) = X2 := superpose eq197 eq222 -- forward demodulation 222,197
  have eq233 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)))) = X2 := superpose eq197 eq232 -- forward demodulation 232,197
  have eq234 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq56 eq233 -- forward demodulation 233,56
  have eq235 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq122 eq234 -- forward demodulation 234,122
  have eq357 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq197 eq20 -- superposition 20,197, 197 into 20, unify on (0).2 in 197 and (0).2 in 20
  subsumption eq357 eq235


@[equational_result]
theorem Equation895_implies_Equation1384 (G : Type*) [Magma G] (h : Equation895 G) : Equation1384 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK2) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.2 in 12
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq36 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1 in 12
  have eq73 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) = X3 := superpose eq17 eq34 -- superposition 34,17, 17 into 34, unify on (0).2 in 17 and (0).1 in 34
  have eq77 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) := superpose eq34 eq9 -- superposition 9,34, 34 into 9, unify on (0).2 in 34 and (0).1.2 in 9
  have eq92 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq77 eq26 -- backward demodulation 26,77
  have eq101 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq92 eq73 -- backward demodulation 73,92
  have eq105 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq101 eq10 -- backward demodulation 10,101
  subsumption eq105 eq36


@[equational_result]
theorem Equation895_implies_Equation2949 (G : Type*) [Magma G] (h : Equation895 G) : Equation2949 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq20 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq22 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1.2.2 in 11
  have eq57 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq17 eq22 -- superposition 22,17, 17 into 22, unify on (0).2 in 17 and (0).1.2 in 22
  have eq322 : sK0 ≠ sK0 := superpose eq57 eq20 -- superposition 20,57, 57 into 20, unify on (0).2 in 57 and (0).2 in 20
  subsumption eq322 rfl


@[equational_result]
theorem Equation895_implies_Equation861 (G : Type*) [Magma G] (h : Equation895 G) : Equation861 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.2 in 12
  have eq33 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2.2 in 11
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq36 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1 in 12
  have eq58 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X2) = X3 := superpose eq17 eq34 -- superposition 34,17, 17 into 34, unify on (0).2 in 17 and (0).1.1.2.1 in 34
  have eq77 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) := superpose eq34 eq9 -- superposition 9,34, 34 into 9, unify on (0).2 in 34 and (0).1.2 in 9
  have eq84 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X4) ◇ ((X5 ◇ X3) ◇ X4))) = (X2 ◇ (X5 ◇ X0)) := superpose eq34 eq12 -- superposition 12,34, 34 into 12, unify on (0).2 in 34 and (0).1.2.1 in 12
  have eq87 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2) = X3 := superpose eq17 eq58 -- forward demodulation 58,17
  have eq88 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X3 := superpose eq36 eq87 -- forward demodulation 87,36
  have eq92 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq77 eq26 -- backward demodulation 26,77
  have eq93 (X0 X2 X4 : G) : (X4 ◇ (X0 ◇ (X4 ◇ X2))) = (X2 ◇ X0) := superpose eq77 eq33 -- backward demodulation 33,77
  have eq116 (X0 X1 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X5) := superpose eq92 eq84 -- forward demodulation 84,92
  have eq134 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3)) = X2 := superpose eq36 eq12 -- superposition 12,36, 36 into 12, unify on (0).2 in 36 and (0).1.2.1.2.2 in 12
  have eq190 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X1 ◇ X0) := superpose eq9 eq88 -- superposition 88,9, 9 into 88, unify on (0).2 in 9 and (0).1.1 in 88
  have eq235 (X0 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = ((X0 ◇ X2) ◇ X5) := superpose eq190 eq116 -- backward demodulation 116,190
  have eq258 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X3 ◇ X2))) = X2 := superpose eq235 eq134 -- backward demodulation 134,235
  have eq271 : sK0 ≠ (sK0 ◇ (sK2 ◇ ((sK2 ◇ sK1) ◇ sK1))) := superpose eq235 eq10 -- backward demodulation 10,235
  have eq287 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X3 ◇ X2) ◇ (X3 ◇ (X1 ◇ X0))))) = X2 := superpose eq235 eq258 -- forward demodulation 258,235
  have eq288 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)))) = X2 := superpose eq235 eq287 -- forward demodulation 287,235
  have eq289 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq88 eq288 -- forward demodulation 288,88
  have eq290 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq93 eq289 -- forward demodulation 289,93
  have eq335 : sK0 ≠ (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := superpose eq235 eq271 -- forward demodulation 271,235
  have eq336 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq290 eq335 -- forward demodulation 335,290
  subsumption eq336 eq17


@[equational_result]
theorem Equation895_implies_Equation1479 (G : Type*) [Magma G] (h : Equation895 G) : Equation1479 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.2 in 12
  have eq33 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2.2 in 11
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq36 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1 in 12
  have eq58 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X2) = X3 := superpose eq17 eq34 -- superposition 34,17, 17 into 34, unify on (0).2 in 17 and (0).1.1.2.1 in 34
  have eq77 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) := superpose eq34 eq9 -- superposition 9,34, 34 into 9, unify on (0).2 in 34 and (0).1.2 in 9
  have eq84 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X4) ◇ ((X5 ◇ X3) ◇ X4))) = (X2 ◇ (X5 ◇ X0)) := superpose eq34 eq12 -- superposition 12,34, 34 into 12, unify on (0).2 in 34 and (0).1.2.1 in 12
  have eq87 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2) = X3 := superpose eq17 eq58 -- forward demodulation 58,17
  have eq88 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X3 := superpose eq36 eq87 -- forward demodulation 87,36
  have eq92 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq77 eq26 -- backward demodulation 26,77
  have eq93 (X0 X2 X4 : G) : (X4 ◇ (X0 ◇ (X4 ◇ X2))) = (X2 ◇ X0) := superpose eq77 eq33 -- backward demodulation 33,77
  have eq116 (X0 X1 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X5) := superpose eq92 eq84 -- forward demodulation 84,92
  have eq134 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3)) = X2 := superpose eq36 eq12 -- superposition 12,36, 36 into 12, unify on (0).2 in 36 and (0).1.2.1.2.2 in 12
  have eq190 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq9 eq88 -- superposition 88,9, 9 into 88, unify on (0).2 in 9 and (0).1.1 in 88
  have eq235 (X0 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = ((X0 ◇ X2) ◇ X5) := superpose eq190 eq116 -- backward demodulation 116,190
  have eq258 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X3 ◇ X2))) = X2 := superpose eq235 eq134 -- backward demodulation 134,235
  have eq286 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X3 ◇ X2) ◇ (X3 ◇ (X1 ◇ X0))))) = X2 := superpose eq235 eq258 -- forward demodulation 258,235
  have eq287 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)))) = X2 := superpose eq235 eq286 -- forward demodulation 286,235
  have eq288 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq88 eq287 -- forward demodulation 287,88
  have eq289 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq93 eq288 -- forward demodulation 288,93
  have eq291 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq289 eq10 -- backward demodulation 10,289
  subsumption eq291 eq88


