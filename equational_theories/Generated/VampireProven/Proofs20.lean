import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation434_implies_Equation413 (G : Type*) [Magma G] (h : Equation434 G) : Equation413 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation434_implies_Equation4131 (G : Type*) [Magma G] (h : Equation434 G) : Equation4131 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq15 eq14


@[equational_result]
theorem Equation434_implies_Equation3925 (G : Type*) [Magma G] (h : Equation434 G) : Equation3925 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 rfl


@[equational_result]
theorem Equation434_implies_Equation1834 (G : Type*) [Magma G] (h : Equation434 G) : Equation1834 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation434_implies_Equation840 (G : Type*) [Magma G] (h : Equation434 G) : Equation840 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq11


@[equational_result]
theorem Equation434_implies_Equation4318 (G : Type*) [Magma G] (h : Equation434 G) : Equation4318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK2 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2 in 13
  subsumption eq17 rfl


@[equational_result]
theorem Equation434_implies_Equation437 (G : Type*) [Magma G] (h : Equation434 G) : Equation437 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2 in 13
  subsumption eq17 rfl


@[equational_result]
theorem Equation434_implies_Equation360 (G : Type*) [Magma G] (h : Equation434 G) : Equation360 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq23 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq23 rfl


@[equational_result]
theorem Equation434_implies_Equation3721 (G : Type*) [Magma G] (h : Equation434 G) : Equation3721 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation434_implies_Equation4314 (G : Type*) [Magma G] (h : Equation434 G) : Equation4314 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2 in 13
  subsumption eq17 rfl


@[equational_result]
theorem Equation434_implies_Equation3943 (G : Type*) [Magma G] (h : Equation434 G) : Equation3943 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 rfl


@[equational_result]
theorem Equation434_implies_Equation1055 (G : Type*) [Magma G] (h : Equation434 G) : Equation1055 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation434_implies_Equation3935 (G : Type*) [Magma G] (h : Equation434 G) : Equation3935 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 rfl


@[equational_result]
theorem Equation434_implies_Equation1857 (G : Type*) [Magma G] (h : Equation434 G) : Equation1857 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq11


@[equational_result]
theorem Equation434_implies_Equation1045 (G : Type*) [Magma G] (h : Equation434 G) : Equation1045 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation434_implies_Equation849 (G : Type*) [Magma G] (h : Equation434 G) : Equation849 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq17 eq12


@[equational_result]
theorem Equation434_implies_Equation1850 (G : Type*) [Magma G] (h : Equation434 G) : Equation1850 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation434_implies_Equation443 (G : Type*) [Magma G] (h : Equation434 G) : Equation443 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2 in 13
  subsumption eq17 rfl


@[equational_result]
theorem Equation434_implies_Equation4067 (G : Type*) [Magma G] (h : Equation434 G) : Equation4067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq16 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq17 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq17 eq14


@[equational_result]
theorem Equation434_implies_Equation832 (G : Type*) [Magma G] (h : Equation434 G) : Equation832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq11


@[equational_result]
theorem Equation434_implies_Equation1049 (G : Type*) [Magma G] (h : Equation434 G) : Equation1049 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2 in 13
  subsumption eq17 rfl


@[equational_result]
theorem Equation434_implies_Equation3255 (G : Type*) [Magma G] (h : Equation434 G) : Equation3255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 rfl


@[equational_result]
theorem Equation434_implies_Equation1039 (G : Type*) [Magma G] (h : Equation434 G) : Equation1039 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2 in 13
  subsumption eq17 rfl


@[equational_result]
theorem Equation434_implies_Equation1860 (G : Type*) [Magma G] (h : Equation434 G) : Equation1860 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq11


@[equational_result]
theorem Equation434_implies_Equation440 (G : Type*) [Magma G] (h : Equation434 G) : Equation440 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2 in 13
  subsumption eq17 rfl


@[equational_result]
theorem Equation434_implies_Equation1851 (G : Type*) [Magma G] (h : Equation434 G) : Equation1851 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2 in 13
  subsumption eq17 rfl


@[equational_result]
theorem Equation434_implies_Equation1855 (G : Type*) [Magma G] (h : Equation434 G) : Equation1855 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2 in 13
  subsumption eq17 rfl


@[equational_result]
theorem Equation434_implies_Equation1863 (G : Type*) [Magma G] (h : Equation434 G) : Equation1863 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq11


@[equational_result]
theorem Equation434_implies_Equation1060 (G : Type*) [Magma G] (h : Equation434 G) : Equation1060 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2 in 13
  subsumption eq17 rfl


@[equational_result]
theorem Equation3064_implies_Equation4284 (G : Type*) [Magma G] (h : Equation3064 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation3064_implies_Equation3259 (G : Type*) [Magma G] (h : Equation3064 G) : Equation3259 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation3064_implies_Equation4629 (G : Type*) [Magma G] (h : Equation3064 G) : Equation4629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X3 X4 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X3) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : ((sK0 ◇ sK0) ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq12


@[equational_result]
theorem Equation3064_implies_Equation3467 (G : Type*) [Magma G] (h : Equation3064 G) : Equation3467 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation3064_implies_Equation3463 (G : Type*) [Magma G] (h : Equation3064 G) : Equation3463 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq13 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 rfl


@[equational_result]
theorem Equation1439_implies_Equation2478 (G : Type*) [Magma G] (h : Equation1439 G) : Equation2478 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq13 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq21 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq21 eq13


@[equational_result]
theorem Equation2251_implies_Equation158 (G : Type*) [Magma G] (h : Equation2251 G) : Equation158 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (X0 ◇ X3) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq36 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X0 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.1 in 11
  have eq46 : sK0 ≠ sK0 := superpose eq36 eq10 -- superposition 10,36, 36 into 10, unify on (0).2 in 36 and (0).2 in 10
  subsumption eq46 rfl


@[equational_result]
theorem Equation644_implies_Equation3926 (G : Type*) [Magma G] (h : Equation644 G) : Equation3926 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq13 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 : sK0 ≠ (sK0 ◇ sK1) := superpose eq13 eq17 -- forward demodulation 17,13
  subsumption eq18 eq13


@[equational_result]
theorem Equation644_implies_Equation1238 (G : Type*) [Magma G] (h : Equation644 G) : Equation1238 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq13


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
theorem Equation644_implies_Equation53 (G : Type*) [Magma G] (h : Equation644 G) : Equation53 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : sK0 ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq13


@[equational_result]
theorem Equation644_implies_Equation3927 (G : Type*) [Magma G] (h : Equation644 G) : Equation3927 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 : sK0 ≠ (sK0 ◇ sK1) := superpose eq13 eq17 -- forward demodulation 17,13
  subsumption eq18 eq13


@[equational_result]
theorem Equation644_implies_Equation55 (G : Type*) [Magma G] (h : Equation644 G) : Equation55 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : sK0 ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq13


@[equational_result]
theorem Equation644_implies_Equation1237 (G : Type*) [Magma G] (h : Equation644 G) : Equation1237 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq13 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK2) ◇ sK3)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq13


@[equational_result]
theorem Equation644_implies_Equation1060 (G : Type*) [Magma G] (h : Equation644 G) : Equation1060 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq13


@[equational_result]
theorem Equation644_implies_Equation4383 (G : Type*) [Magma G] (h : Equation644 G) : Equation4383 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 : sK0 ≠ (sK0 ◇ sK1) := superpose eq13 eq17 -- forward demodulation 17,13
  subsumption eq18 eq13


@[equational_result]
theorem Equation644_implies_Equation4434 (G : Type*) [Magma G] (h : Equation644 G) : Equation4434 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq13 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 : sK0 ≠ (sK0 ◇ sK2) := superpose eq13 eq17 -- forward demodulation 17,13
  subsumption eq18 eq13


@[equational_result]
theorem Equation644_implies_Equation433 (G : Type*) [Magma G] (h : Equation644 G) : Equation433 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq13 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq13


@[equational_result]
theorem Equation644_implies_Equation2486 (G : Type*) [Magma G] (h : Equation644 G) : Equation2486 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq13 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : sK0 ≠ (sK0 ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq13


@[equational_result]
theorem Equation644_implies_Equation640 (G : Type*) [Magma G] (h : Equation644 G) : Equation640 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq13 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : sK0 ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq13


@[equational_result]
theorem Equation2977_implies_Equation1428 (G : Type*) [Magma G] (h : Equation2977 G) : Equation1428 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X2 X3 : G) : (((X3 ◇ X2) ◇ X3) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq34 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.1 in 9
  have eq62 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := superpose eq34 eq10 -- backward demodulation 10,34
  have eq63 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq34 eq62 -- forward demodulation 62,34
  subsumption eq63 eq34


@[equational_result]
theorem Equation2977_implies_Equation2509 (G : Type*) [Magma G] (h : Equation2977 G) : Equation2509 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK1) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : (((X3 ◇ X2) ◇ X3) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq34 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.1 in 9
  have eq62 : sK0 ≠ ((sK1 ◇ sK2) ◇ sK0) := superpose eq34 eq10 -- backward demodulation 10,34
  subsumption eq62 eq34


@[equational_result]
theorem Equation1713_implies_Equation3292 (G : Type*) [Magma G] (h : Equation1713 G) : Equation3292 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq12 (X1 X4 X5 : G) : ((X4 ◇ X5) ◇ (X1 ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X1) = ((X4 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq27 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq35 (X1 X4 : G) : (X1 ◇ X4) = (X4 ◇ X4) := superpose eq9 eq27 -- superposition 27,9, 9 into 27, unify on (0).2 in 9 and (0).1.1 in 27
  have eq67 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := superpose eq35 eq10 -- backward demodulation 10,35
  have eq73 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq12 eq35 -- superposition 35,12, 12 into 35, unify on (0).2 in 12 and (0).2 in 35
  have eq105 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq73 eq67 -- backward demodulation 67,73
  subsumption eq105 eq35


@[equational_result]
theorem Equation1713_implies_Equation1167 (G : Type*) [Magma G] (h : Equation1713 G) : Equation1167 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X4 X5 : G) : ((X4 ◇ X5) ◇ (X1 ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X1) = ((X4 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq27 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ X3) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq35 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq27 eq10 -- backward demodulation 10,27
  have eq63 (X1 X4 : G) : (X1 ◇ X4) = (X4 ◇ X4) := superpose eq9 eq27 -- superposition 27,9, 9 into 27, unify on (0).2 in 9 and (0).2.1 in 27
  have eq127 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq12 eq63 -- superposition 63,12, 12 into 63, unify on (0).2 in 12 and (0).2 in 63
  have eq158 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ sK0)) := superpose eq63 eq35 -- superposition 35,63, 63 into 35, unify on (0).2 in 63 and (0).2.2 in 35
  subsumption eq158 eq127


@[equational_result]
theorem Equation1713_implies_Equation516 (G : Type*) [Magma G] (h : Equation1713 G) : Equation516 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq12 (X1 X4 X5 : G) : ((X4 ◇ X5) ◇ (X1 ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X1) = ((X4 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq27 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq35 (X1 X4 : G) : (X1 ◇ X4) = (X4 ◇ X4) := superpose eq9 eq27 -- superposition 27,9, 9 into 27, unify on (0).2 in 9 and (0).1.1 in 27
  have eq67 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := superpose eq35 eq10 -- backward demodulation 10,35
  have eq73 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq12 eq35 -- superposition 35,12, 12 into 35, unify on (0).2 in 12 and (0).2 in 35
  have eq105 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq73 eq67 -- backward demodulation 67,73
  subsumption eq105 eq73


@[equational_result]
theorem Equation1713_implies_Equation3326 (G : Type*) [Magma G] (h : Equation1713 G) : Equation3326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X1 X4 X5 : G) : ((X4 ◇ X5) ◇ (X1 ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X1) = ((X4 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq27 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq35 (X1 X4 : G) : (X1 ◇ X4) = (X4 ◇ X4) := superpose eq9 eq27 -- superposition 27,9, 9 into 27, unify on (0).2 in 9 and (0).1.1 in 27
  have eq93 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq12 eq35 -- superposition 35,12, 12 into 35, unify on (0).2 in 12 and (0).2 in 35
  have eq128 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq93 eq10 -- backward demodulation 10,93
  subsumption eq128 rfl


@[equational_result]
theorem Equation1713_implies_Equation1728 (G : Type*) [Magma G] (h : Equation1713 G) : Equation1728 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X4 X5 : G) : ((X4 ◇ X5) ◇ (X1 ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X1) = ((X4 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq27 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ X3) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq35 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := superpose eq27 eq10 -- backward demodulation 10,27
  have eq93 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq27 eq35 -- superposition 35,27, 27 into 35, unify on (0).2 in 27 and (0).2 in 35
  subsumption eq93 eq12


@[equational_result]
theorem Equation2454_implies_Equation1439 (G : Type*) [Magma G] (h : Equation2454 G) : Equation1439 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq14 rfl


@[equational_result]
theorem Equation3101_implies_Equation3461 (G : Type*) [Magma G] (h : Equation3101 G) : Equation3461 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X0 ◇ X1) = (X0 ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation3101_implies_Equation3267 (G : Type*) [Magma G] (h : Equation3101 G) : Equation3267 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X0 ◇ X1) = (X0 ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation3101_implies_Equation3320 (G : Type*) [Magma G] (h : Equation3101 G) : Equation3320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X0 ◇ X1) = (X0 ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation3101_implies_Equation3535 (G : Type*) [Magma G] (h : Equation3101 G) : Equation3535 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK1) ◇ sK3)) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X0 ◇ X1) = (X0 ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK1) ◇ X0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation3101_implies_Equation327 (G : Type*) [Magma G] (h : Equation3101 G) : Equation327 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X0 ◇ X1) = (X0 ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation3101_implies_Equation311 (G : Type*) [Magma G] (h : Equation3101 G) : Equation311 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X0 ◇ X1) = (X0 ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation3101_implies_Equation325 (G : Type*) [Magma G] (h : Equation3101 G) : Equation325 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X0 ◇ X1) = (X0 ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation2085_implies_Equation2851 (G : Type*) [Magma G] (h : Equation2085 G) : Equation2851 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X0 ◇ X1) = (X0 ◇ (X4 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X4) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 (X0 : G) : sK0 ≠ (((sK0 ◇ (X0 ◇ X0)) ◇ sK1) ◇ sK2) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1.1 in 10
  subsumption eq23 eq13


@[equational_result]
theorem Equation3587_implies_Equation4483 (G : Type*) [Magma G] (h : Equation3587 G) : Equation4483 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK1 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq30 : (sK1 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq30 rfl


@[equational_result]
theorem Equation3587_implies_Equation3877 (G : Type*) [Magma G] (h : Equation3587 G) : Equation3877 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq28 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq28 rfl


@[equational_result]
theorem Equation3587_implies_Equation3993 (G : Type*) [Magma G] (h : Equation3587 G) : Equation3993 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq28 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq28 rfl


@[equational_result]
theorem Equation3587_implies_Equation378 (G : Type*) [Magma G] (h : Equation3587 G) : Equation378 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq17 (X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq27 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq27 rfl


@[equational_result]
theorem Equation3587_implies_Equation3353 (G : Type*) [Magma G] (h : Equation3587 G) : Equation3353 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation3587_implies_Equation3820 (G : Type*) [Magma G] (h : Equation3587 G) : Equation3820 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq20 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation3587_implies_Equation4533 (G : Type*) [Magma G] (h : Equation3587 G) : Equation4533 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK1 ◇ sK2) ≠ ((sK1 ◇ sK2) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq30 : (sK1 ◇ sK2) ≠ (sK1 ◇ sK2) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq30 rfl


@[equational_result]
theorem Equation3587_implies_Equation3955 (G : Type*) [Magma G] (h : Equation3587 G) : Equation3955 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq28 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq28 rfl


@[equational_result]
theorem Equation3587_implies_Equation3431 (G : Type*) [Magma G] (h : Equation3587 G) : Equation3431 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation3587_implies_Equation3837 (G : Type*) [Magma G] (h : Equation3587 G) : Equation3837 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK3) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq20 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation3587_implies_Equation323 (G : Type*) [Magma G] (h : Equation3587 G) : Equation323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3587_implies_Equation3343 (G : Type*) [Magma G] (h : Equation3587 G) : Equation3343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation3587_implies_Equation3803 (G : Type*) [Magma G] (h : Equation3587 G) : Equation3803 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3587_implies_Equation4065 (G : Type*) [Magma G] (h : Equation3587 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1 in 8
  have eq12 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq8 eq10 -- forward demodulation 10,8
  have eq16 (X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2 in 12
  have eq21 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq16 eq9 -- backward demodulation 9,16
  subsumption eq21 eq16


@[equational_result]
theorem Equation3587_implies_Equation4442 (G : Type*) [Magma G] (h : Equation3587 G) : Equation4442 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK1 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq30 : (sK1 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq30 rfl


@[equational_result]
theorem Equation3587_implies_Equation3414 (G : Type*) [Magma G] (h : Equation3587 G) : Equation3414 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation3587_implies_Equation3732 (G : Type*) [Magma G] (h : Equation3587 G) : Equation3732 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3587_implies_Equation333 (G : Type*) [Magma G] (h : Equation3587 G) : Equation333 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq21 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation3587_implies_Equation343 (G : Type*) [Magma G] (h : Equation3587 G) : Equation343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq21 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation537_implies_Equation4635 (G : Type*) [Magma G] (h : Equation537 G) : Equation4635 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2.2 in 9
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq26 -- forward demodulation 26,9
  have eq79 (X0 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ ((X0 ◇ sK0) ◇ sK0) := superpose eq30 eq10 -- superposition 10,30, 30 into 10, unify on (0).2 in 30 and (0).2.1 in 10
  subsumption eq79 eq30


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
theorem Equation537_implies_Equation4677 (G : Type*) [Magma G] (h : Equation537 G) : Equation4677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK1 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2.2 in 9
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq26 -- forward demodulation 26,9
  have eq67 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ ((X0 ◇ sK0) ◇ sK2) := superpose eq30 eq10 -- superposition 10,30, 30 into 10, unify on (0).2 in 30 and (0).2.1 in 10
  subsumption eq67 eq30


@[equational_result]
theorem Equation537_implies_Equation4080 (G : Type*) [Magma G] (h : Equation537 G) : Equation4080 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2.2 in 9
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq26 -- forward demodulation 26,9
  have eq79 (X0 : G) : (sK0 ◇ sK0) ≠ (((X0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq30 eq10 -- superposition 10,30, 30 into 10, unify on (0).2 in 30 and (0).2.1.1 in 10
  subsumption eq79 eq30


@[equational_result]
theorem Equation537_implies_Equation3993 (G : Type*) [Magma G] (h : Equation537 G) : Equation3993 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq28 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2.2 in 9
  have eq32 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq28 -- forward demodulation 28,9
  have eq51 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq32 eq14 -- superposition 14,32, 32 into 14, unify on (0).2 in 32 and (0).2 in 14
  subsumption eq51 eq32


@[equational_result]
theorem Equation537_implies_Equation4001 (G : Type*) [Magma G] (h : Equation537 G) : Equation4001 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK0 ◇ sK3)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2.2 in 9
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq26 -- forward demodulation 26,9
  have eq79 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq30 eq10 -- superposition 10,30, 30 into 10, unify on (0).2 in 30 and (0).2 in 10
  subsumption eq79 eq30


@[equational_result]
theorem Equation459_implies_Equation450 (G : Type*) [Magma G] (h : Equation459 G) : Equation450 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq17 : sK0 ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq15


@[equational_result]
theorem Equation459_implies_Equation1045 (G : Type*) [Magma G] (h : Equation459 G) : Equation1045 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq15


@[equational_result]
theorem Equation459_implies_Equation3732 (G : Type*) [Magma G] (h : Equation459 G) : Equation3732 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq17 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK0) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq19 : sK0 ≠ (sK0 ◇ sK0) := superpose eq15 eq17 -- forward demodulation 17,15
  subsumption eq19 eq15


@[equational_result]
theorem Equation459_implies_Equation2671 (G : Type*) [Magma G] (h : Equation459 G) : Equation2671 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq17 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq19 : sK0 ≠ (sK0 ◇ sK2) := superpose eq15 eq17 -- forward demodulation 17,15
  subsumption eq19 eq15


@[equational_result]
theorem Equation459_implies_Equation3935 (G : Type*) [Magma G] (h : Equation459 G) : Equation3935 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 rfl


@[equational_result]
theorem Equation459_implies_Equation1024 (G : Type*) [Magma G] (h : Equation459 G) : Equation1024 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq17 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK2)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq15


@[equational_result]
theorem Equation459_implies_Equation3100 (G : Type*) [Magma G] (h : Equation459 G) : Equation3100 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK3) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq17 : sK0 ≠ (((sK0 ◇ sK2) ◇ sK3) ◇ sK3) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq19 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK3) := superpose eq15 eq17 -- forward demodulation 17,15
  have eq20 : sK0 ≠ (sK0 ◇ sK3) := superpose eq15 eq19 -- forward demodulation 19,15
  subsumption eq20 eq15


@[equational_result]
theorem Equation459_implies_Equation3712 (G : Type*) [Magma G] (h : Equation459 G) : Equation3712 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq19 : sK0 ≠ (sK0 ◇ sK1) := superpose eq15 eq17 -- forward demodulation 17,15
  subsumption eq19 eq15


@[equational_result]
theorem Equation459_implies_Equation828 (G : Type*) [Magma G] (h : Equation459 G) : Equation828 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq17 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq15


@[equational_result]
theorem Equation459_implies_Equation829 (G : Type*) [Magma G] (h : Equation459 G) : Equation829 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq17 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq15


@[equational_result]
theorem Equation459_implies_Equation3917 (G : Type*) [Magma G] (h : Equation459 G) : Equation3917 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq19 : sK0 ≠ (sK0 ◇ sK1) := superpose eq15 eq17 -- forward demodulation 17,15
  subsumption eq19 eq15


@[equational_result]
theorem Equation459_implies_Equation1439 (G : Type*) [Magma G] (h : Equation459 G) : Equation1439 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq17 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq19 : sK0 ≠ (sK0 ◇ sK1) := superpose eq15 eq17 -- forward demodulation 17,15
  subsumption eq19 eq15


@[equational_result]
theorem Equation459_implies_Equation4518 (G : Type*) [Magma G] (h : Equation459 G) : Equation4518 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK3) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq17 : sK0 ≠ ((sK0 ◇ sK3) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq19 : sK0 ≠ (sK0 ◇ sK0) := superpose eq15 eq17 -- forward demodulation 17,15
  subsumption eq19 eq15


@[equational_result]
theorem Equation541_implies_Equation479 (G : Type*) [Magma G] (h : Equation541 G) : Equation479 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = (X0 ◇ (X3 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = (X0 ◇ (X3 ◇ (X2 ◇ X2))) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq14 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2.2 in 9
  have eq101 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.2 in 14
  subsumption eq101 eq16


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
theorem Equation2982_implies_Equation749 (G : Type*) [Magma G] (h : Equation2982 G) : Equation749 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X3 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X3) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.2 in 13
  have eq50 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1.2 in 16
  have eq76 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = X1 := superpose eq50 eq16 -- backward demodulation 16,50
  have eq79 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := superpose eq50 eq10 -- backward demodulation 10,50
  subsumption eq79 eq76


@[equational_result]
theorem Equation2982_implies_Equation511 (G : Type*) [Magma G] (h : Equation2982 G) : Equation511 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X3 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X3) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.2 in 13
  have eq50 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1.2 in 16
  have eq76 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = X1 := superpose eq50 eq16 -- backward demodulation 16,50
  have eq438 : sK0 ≠ sK0 := superpose eq76 eq10 -- superposition 10,76, 76 into 10, unify on (0).2 in 76 and (0).2 in 10
  subsumption eq438 rfl


@[equational_result]
theorem Equation428_implies_Equation105 (G : Type*) [Magma G] (h : Equation428 G) : Equation105 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.2 in 12
  have eq32 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq31 eq10 -- backward demodulation 10,31
  subsumption eq32 eq12


@[equational_result]
theorem Equation428_implies_Equation3928 (G : Type*) [Magma G] (h : Equation428 G) : Equation3928 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq37 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq37 rfl


@[equational_result]
theorem Equation428_implies_Equation1067 (G : Type*) [Magma G] (h : Equation428 G) : Equation1067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq24 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq24 rfl


@[equational_result]
theorem Equation428_implies_Equation4131 (G : Type*) [Magma G] (h : Equation428 G) : Equation4131 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq24 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq19 eq10 -- backward demodulation 10,19
  subsumption eq24 eq19


@[equational_result]
theorem Equation428_implies_Equation3925 (G : Type*) [Magma G] (h : Equation428 G) : Equation3925 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 rfl


@[equational_result]
theorem Equation428_implies_Equation52 (G : Type*) [Magma G] (h : Equation428 G) : Equation52 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq12


@[equational_result]
theorem Equation428_implies_Equation4286 (G : Type*) [Magma G] (h : Equation428 G) : Equation4286 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq33 : sK0 ≠ sK0 := superpose eq23 eq14 -- superposition 14,23, 23 into 14, unify on (0).2 in 23 and (0).2 in 14
  subsumption eq33 rfl


@[equational_result]
theorem Equation428_implies_Equation3467 (G : Type*) [Magma G] (h : Equation428 G) : Equation3467 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation428_implies_Equation3661 (G : Type*) [Magma G] (h : Equation428 G) : Equation3661 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq12


@[equational_result]
theorem Equation428_implies_Equation2466 (G : Type*) [Magma G] (h : Equation428 G) : Equation2466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation428_implies_Equation1232 (G : Type*) [Magma G] (h : Equation428 G) : Equation1232 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq24 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq25 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq19 eq24 -- forward demodulation 24,19
  have eq33 : sK0 ≠ sK0 := superpose eq22 eq25 -- superposition 25,22, 22 into 25, unify on (0).2 in 22 and (0).2 in 25
  subsumption eq33 rfl


@[equational_result]
theorem Equation428_implies_Equation3461 (G : Type*) [Magma G] (h : Equation428 G) : Equation3461 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation428_implies_Equation1024 (G : Type*) [Magma G] (h : Equation428 G) : Equation1024 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq27 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK2)) := superpose eq22 eq10 -- backward demodulation 10,22
  subsumption eq27 eq22


@[equational_result]
theorem Equation428_implies_Equation822 (G : Type*) [Magma G] (h : Equation428 G) : Equation822 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq12


@[equational_result]
theorem Equation428_implies_Equation1849 (G : Type*) [Magma G] (h : Equation428 G) : Equation1849 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq33 : sK0 ≠ sK0 := superpose eq23 eq14 -- superposition 14,23, 23 into 14, unify on (0).2 in 23 and (0).2 in 14
  subsumption eq33 rfl


@[equational_result]
theorem Equation428_implies_Equation4472 (G : Type*) [Magma G] (h : Equation428 G) : Equation4472 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.2 in 12
  have eq44 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq15 -- superposition 15,32, 32 into 15, unify on (0).2 in 32 and (0).2 in 15
  subsumption eq44 rfl


@[equational_result]
theorem Equation428_implies_Equation842 (G : Type*) [Magma G] (h : Equation428 G) : Equation842 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq12


@[equational_result]
theorem Equation428_implies_Equation1242 (G : Type*) [Magma G] (h : Equation428 G) : Equation1242 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq24 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.2 in 12
  have eq33 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq32 eq24 -- backward demodulation 24,32
  subsumption eq33 eq12


@[equational_result]
theorem Equation428_implies_Equation3918 (G : Type*) [Magma G] (h : Equation428 G) : Equation3918 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq27 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq22 eq10 -- backward demodulation 10,22
  subsumption eq27 rfl


@[equational_result]
theorem Equation428_implies_Equation2649 (G : Type*) [Magma G] (h : Equation428 G) : Equation2649 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq13


@[equational_result]
theorem Equation428_implies_Equation2446 (G : Type*) [Magma G] (h : Equation428 G) : Equation2446 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation428_implies_Equation1036 (G : Type*) [Magma G] (h : Equation428 G) : Equation1036 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.2 in 12
  have eq33 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq32 eq15 -- backward demodulation 15,32
  subsumption eq33 eq12


@[equational_result]
theorem Equation428_implies_Equation1631 (G : Type*) [Magma G] (h : Equation428 G) : Equation1631 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq12


@[equational_result]
theorem Equation428_implies_Equation1634 (G : Type*) [Magma G] (h : Equation428 G) : Equation1634 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq12


@[equational_result]
theorem Equation428_implies_Equation4283 (G : Type*) [Magma G] (h : Equation428 G) : Equation4283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq33 : sK0 ≠ sK0 := superpose eq23 eq14 -- superposition 14,23, 23 into 14, unify on (0).2 in 23 and (0).2 in 14
  subsumption eq33 rfl


@[equational_result]
theorem Equation428_implies_Equation377 (G : Type*) [Magma G] (h : Equation428 G) : Equation377 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.2 in 12
  have eq43 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq31 eq10 -- superposition 10,31, 31 into 10, unify on (0).2 in 31 and (0).2 in 10
  subsumption eq43 rfl


@[equational_result]
theorem Equation428_implies_Equation1843 (G : Type*) [Magma G] (h : Equation428 G) : Equation1843 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq27 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK0)) := superpose eq22 eq10 -- backward demodulation 10,22
  subsumption eq27 eq12


@[equational_result]
theorem Equation428_implies_Equation1840 (G : Type*) [Magma G] (h : Equation428 G) : Equation1840 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq27 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq22 eq10 -- backward demodulation 10,22
  subsumption eq27 eq12


@[equational_result]
theorem Equation428_implies_Equation835 (G : Type*) [Magma G] (h : Equation428 G) : Equation835 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq12


@[equational_result]
theorem Equation428_implies_Equation2037 (G : Type*) [Magma G] (h : Equation428 G) : Equation2037 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq15 -- forward demodulation 15,13
  subsumption eq16 eq12


@[equational_result]
theorem Equation428_implies_Equation4121 (G : Type*) [Magma G] (h : Equation428 G) : Equation4121 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq37 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq37 rfl


@[equational_result]
theorem Equation428_implies_Equation3721 (G : Type*) [Magma G] (h : Equation428 G) : Equation3721 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.2 in 12
  have eq44 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq15 -- superposition 15,32, 32 into 15, unify on (0).2 in 32 and (0).2 in 15
  subsumption eq44 rfl


@[equational_result]
theorem Equation428_implies_Equation1026 (G : Type*) [Magma G] (h : Equation428 G) : Equation1026 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq33 : sK0 ≠ sK0 := superpose eq23 eq14 -- superposition 14,23, 23 into 14, unify on (0).2 in 23 and (0).2 in 14
  subsumption eq33 rfl


@[equational_result]
theorem Equation428_implies_Equation2253 (G : Type*) [Magma G] (h : Equation428 G) : Equation2253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation428_implies_Equation3927 (G : Type*) [Magma G] (h : Equation428 G) : Equation3927 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.2 in 12
  have eq44 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq15 -- superposition 15,32, 32 into 15, unify on (0).2 in 32 and (0).2 in 15
  subsumption eq44 rfl


@[equational_result]
theorem Equation428_implies_Equation4599 (G : Type*) [Magma G] (h : Equation428 G) : Equation4599 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq39 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq39 rfl


@[equational_result]
theorem Equation428_implies_Equation4629 (G : Type*) [Magma G] (h : Equation428 G) : Equation4629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq24 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.2 in 12
  have eq47 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq24 -- superposition 24,32, 32 into 24, unify on (0).2 in 32 and (0).2 in 24
  subsumption eq47 rfl


@[equational_result]
theorem Equation428_implies_Equation4598 (G : Type*) [Magma G] (h : Equation428 G) : Equation4598 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.2 in 12
  have eq44 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq15 -- superposition 15,32, 32 into 15, unify on (0).2 in 32 and (0).2 in 15
  subsumption eq44 rfl


@[equational_result]
theorem Equation428_implies_Equation4473 (G : Type*) [Magma G] (h : Equation428 G) : Equation4473 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq39 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq39 rfl


@[equational_result]
theorem Equation428_implies_Equation4130 (G : Type*) [Magma G] (h : Equation428 G) : Equation4130 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq24 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.2 in 12
  have eq47 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq24 -- superposition 24,32, 32 into 24, unify on (0).2 in 32 and (0).2 in 24
  subsumption eq47 rfl


@[equational_result]
theorem Equation428_implies_Equation4120 (G : Type*) [Magma G] (h : Equation428 G) : Equation4120 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.2 in 12
  have eq44 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq15 -- superposition 15,32, 32 into 15, unify on (0).2 in 32 and (0).2 in 15
  subsumption eq44 rfl


@[equational_result]
theorem Equation428_implies_Equation3725 (G : Type*) [Magma G] (h : Equation428 G) : Equation3725 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq39 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq39 rfl


@[equational_result]
theorem Equation428_implies_Equation3462 (G : Type*) [Magma G] (h : Equation428 G) : Equation3462 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.2 in 12
  have eq33 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq32 eq15 -- backward demodulation 15,32
  subsumption eq33 eq12


@[equational_result]
theorem Equation428_implies_Equation3258 (G : Type*) [Magma G] (h : Equation428 G) : Equation3258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation428_implies_Equation2862 (G : Type*) [Magma G] (h : Equation428 G) : Equation2862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq14 -- backward demodulation 14,13
  subsumption eq16 eq13


@[equational_result]
theorem Equation428_implies_Equation2459 (G : Type*) [Magma G] (h : Equation428 G) : Equation2459 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.2 in 12
  have eq32 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq31 eq10 -- backward demodulation 10,31
  have eq33 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq32 -- forward demodulation 32,12
  subsumption eq33 eq13


@[equational_result]
theorem Equation428_implies_Equation1637 (G : Type*) [Magma G] (h : Equation428 G) : Equation1637 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq12


@[equational_result]
theorem Equation428_implies_Equation1249 (G : Type*) [Magma G] (h : Equation428 G) : Equation1249 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.2 in 12
  have eq33 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq32 eq15 -- backward demodulation 15,32
  subsumption eq33 eq12


@[equational_result]
theorem Equation428_implies_Equation1239 (G : Type*) [Magma G] (h : Equation428 G) : Equation1239 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq24 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.2 in 12
  have eq33 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq32 eq24 -- backward demodulation 24,32
  subsumption eq33 eq12


@[equational_result]
theorem Equation428_implies_Equation1229 (G : Type*) [Magma G] (h : Equation428 G) : Equation1229 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.2 in 12
  have eq32 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := superpose eq31 eq10 -- backward demodulation 10,31
  have eq33 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq19 eq32 -- forward demodulation 32,19
  subsumption eq33 eq22


@[equational_result]
theorem Equation428_implies_Equation836 (G : Type*) [Magma G] (h : Equation428 G) : Equation836 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.2 in 12
  have eq33 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq32 eq15 -- backward demodulation 15,32
  subsumption eq33 eq12


@[equational_result]
theorem Equation428_implies_Equation4432 (G : Type*) [Magma G] (h : Equation428 G) : Equation4432 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq14 -- backward demodulation 14,13
  subsumption eq16 eq13


@[equational_result]
theorem Equation428_implies_Equation1640 (G : Type*) [Magma G] (h : Equation428 G) : Equation1640 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq12


@[equational_result]
theorem Equation428_implies_Equation102 (G : Type*) [Magma G] (h : Equation428 G) : Equation102 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq24 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq32 : sK0 ≠ sK0 := superpose eq22 eq24 -- superposition 24,22, 22 into 24, unify on (0).2 in 22 and (0).2 in 24
  subsumption eq32 rfl


@[equational_result]
theorem Equation428_implies_Equation1027 (G : Type*) [Magma G] (h : Equation428 G) : Equation1027 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq33 : sK0 ≠ sK0 := superpose eq23 eq14 -- superposition 14,23, 23 into 14, unify on (0).2 in 23 and (0).2 in 14
  subsumption eq33 rfl


@[equational_result]
theorem Equation3879_implies_Equation3905 (G : Type*) [Magma G] (h : Equation3879 G) : Equation3905 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq45 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq20 eq13 -- superposition 13,20, 20 into 13, unify on (0).2 in 20 and (0).2 in 13
  subsumption eq45 eq20


@[equational_result]
theorem Equation3879_implies_Equation40 (G : Type*) [Magma G] (h : Equation3879 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq12 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq38 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq38 eq19


@[equational_result]
theorem Equation3879_implies_Equation3908 (G : Type*) [Magma G] (h : Equation3879 G) : Equation3908 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK3) := mod_symm nh
  have eq12 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq45 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq20 eq13 -- superposition 13,20, 20 into 13, unify on (0).2 in 20 and (0).2 in 13
  subsumption eq45 eq20


@[equational_result]
theorem Equation3879_implies_Equation3665 (G : Type*) [Magma G] (h : Equation3879 G) : Equation3665 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq22 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ X1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 eq12


@[equational_result]
theorem Equation1870_implies_Equation1646 (G : Type*) [Magma G] (h : Equation1870 G) : Equation1646 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ X0) ◇ (X4 ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq27 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq46 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := superpose eq27 eq10 -- superposition 10,27, 27 into 10, unify on (0).2 in 27 and (0).2 in 10
  subsumption eq46 eq11


@[equational_result]
theorem Equation662_implies_Equation256 (G : Type*) [Magma G] (h : Equation662 G) : Equation256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X5))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq14 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0)) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq16 eq14 -- backward demodulation 14,16
  have eq25 (X4 X5 : G) : (X4 ◇ X5) = X4 := superpose eq21 eq11 -- backward demodulation 11,21
  have eq29 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq25 eq10 -- backward demodulation 10,25
  have eq30 : sK0 ≠ (sK0 ◇ sK1) := superpose eq25 eq29 -- forward demodulation 29,25
  subsumption eq30 eq25


@[equational_result]
theorem Equation662_implies_Equation1261 (G : Type*) [Magma G] (h : Equation662 G) : Equation1261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ sK3)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X5))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq14 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0)) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq16 eq14 -- backward demodulation 14,16
  have eq25 (X4 X5 : G) : (X4 ◇ X5) = X4 := superpose eq21 eq11 -- backward demodulation 11,21
  have eq29 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK3)) := superpose eq25 eq10 -- backward demodulation 10,25
  subsumption eq29 eq25


@[equational_result]
theorem Equation662_implies_Equation3926 (G : Type*) [Magma G] (h : Equation662 G) : Equation3926 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X5))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq14 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0)) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq16 eq14 -- backward demodulation 14,16
  have eq25 (X4 X5 : G) : (X4 ◇ X5) = X4 := superpose eq21 eq11 -- backward demodulation 11,21
  have eq26 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK2) := superpose eq21 eq10 -- backward demodulation 10,21
  have eq30 : sK0 ≠ (sK0 ◇ sK1) := superpose eq25 eq26 -- forward demodulation 26,25
  subsumption eq30 eq25


