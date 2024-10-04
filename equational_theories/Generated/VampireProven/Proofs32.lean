import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation412_implies_Equation3050 (G : Type*) [Magma G] (h : Equation412 G) : Equation3050 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq10 -- backward demodulation 10,11
  have eq15 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq13 eq9 -- backward demodulation 9,13
  have eq16 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq17 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq16 -- forward demodulation 16,13
  subsumption eq17 eq13


@[equational_result]
theorem Equation412_implies_Equation1629 (G : Type*) [Magma G] (h : Equation412 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq10 -- backward demodulation 10,11
  have eq15 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq13 eq9 -- backward demodulation 9,13
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq15 -- forward demodulation 15,13
  subsumption eq16 eq13


@[equational_result]
theorem Equation412_implies_Equation817 (G : Type*) [Magma G] (h : Equation412 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq10 -- backward demodulation 10,11
  have eq15 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq13 eq9 -- backward demodulation 9,13
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq15 -- forward demodulation 15,13
  subsumption eq16 eq13


@[equational_result]
theorem Equation412_implies_Equation2238 (G : Type*) [Magma G] (h : Equation412 G) : Equation2238 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq10 eq9 -- backward demodulation 9,10
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq10 -- backward demodulation 10,11
  have eq17 : sK0 ≠ sK0 := superpose eq14 eq13 -- superposition 13,14, 14 into 13, unify on (0).2 in 14 and (0).2 in 13
  subsumption eq17 rfl


@[equational_result]
theorem Equation412_implies_Equation2644 (G : Type*) [Magma G] (h : Equation412 G) : Equation2644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq10 -- backward demodulation 10,11
  have eq15 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq13 eq9 -- backward demodulation 9,13
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq15 -- forward demodulation 15,13
  subsumption eq16 eq13


@[equational_result]
theorem Equation412_implies_Equation2441 (G : Type*) [Magma G] (h : Equation412 G) : Equation2441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq10 -- backward demodulation 10,11
  have eq15 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq13 eq9 -- backward demodulation 9,13
  have eq16 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq17 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq16 -- forward demodulation 16,13
  subsumption eq17 eq13


@[equational_result]
theorem Equation412_implies_Equation3715 (G : Type*) [Magma G] (h : Equation412 G) : Equation3715 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq17 rfl


@[equational_result]
theorem Equation412_implies_Equation203 (G : Type*) [Magma G] (h : Equation412 G) : Equation203 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq10 -- backward demodulation 10,11
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq14 eq13


@[equational_result]
theorem Equation412_implies_Equation3 (G : Type*) [Magma G] (h : Equation412 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq10 -- backward demodulation 10,11
  have eq15 : sK0 ≠ sK0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2 in 9
  subsumption eq15 rfl


@[equational_result]
theorem Equation412_implies_Equation2035 (G : Type*) [Magma G] (h : Equation412 G) : Equation2035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq10 -- backward demodulation 10,11
  have eq15 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq13 eq9 -- backward demodulation 9,13
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq15 -- forward demodulation 15,13
  subsumption eq16 eq13


@[equational_result]
theorem Equation412_implies_Equation47 (G : Type*) [Magma G] (h : Equation412 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq10 -- backward demodulation 10,11
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq14 eq13


@[equational_result]
theorem Equation412_implies_Equation3722 (G : Type*) [Magma G] (h : Equation412 G) : Equation3722 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation412_implies_Equation255 (G : Type*) [Magma G] (h : Equation412 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq10 -- backward demodulation 10,11
  have eq15 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq13 eq9 -- backward demodulation 9,13
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq15 -- forward demodulation 15,13
  subsumption eq16 eq13


@[equational_result]
theorem Equation412_implies_Equation3456 (G : Type*) [Magma G] (h : Equation412 G) : Equation3456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq10 -- backward demodulation 10,11
  have eq15 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq13 eq9 -- backward demodulation 9,13
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq15 -- forward demodulation 15,13
  subsumption eq16 eq13


@[equational_result]
theorem Equation229_implies_Equation99 (G : Type*) [Magma G] (h : Equation229 G) : Equation99 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq17 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.2 in 8
  have eq18 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq17 eq9 -- backward demodulation 9,17
  subsumption eq18 eq11


@[equational_result]
theorem Equation229_implies_Equation255 (G : Type*) [Magma G] (h : Equation229 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq17 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.2 in 8
  have eq18 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq17 eq9 -- backward demodulation 9,17
  subsumption eq18 eq8


@[equational_result]
theorem Equation229_implies_Equation4380 (G : Type*) [Magma G] (h : Equation229 G) : Equation4380 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.2 in 8
  have eq18 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2 in 9
  subsumption eq18 rfl


@[equational_result]
theorem Equation229_implies_Equation47 (G : Type*) [Magma G] (h : Equation229 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq15 rfl


@[equational_result]
theorem Equation2053_implies_Equation3253 (G : Type*) [Magma G] (h : Equation2053 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq13 rfl


@[equational_result]
theorem Equation4453_implies_Equation4463 (G : Type*) [Magma G] (h : Equation4453 G) : Equation4463 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK2) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X1) = ((X3 ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = ((X1 ◇ (X2 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK3 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = ((X4 ◇ X2) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq74 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = ((X3 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).2 in 15
  have eq77 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) = ((X3 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq100 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) = (X0 ◇ (X2 ◇ X0)) := superpose eq74 eq77 -- forward demodulation 77,74
  have eq101 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq74 eq100 -- forward demodulation 100,74
  have eq140 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = ((X3 ◇ ((X1 ◇ X0) ◇ X3)) ◇ X2) := superpose eq15 eq21 -- superposition 21,15, 15 into 21, unify on (0).2 in 15 and (0).2 in 21
  have eq630 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = (X1 ◇ (X3 ◇ X1)) := superpose eq101 eq101 -- superposition 101,101, 101 into 101, unify on (0).2 in 101 and (0).2 in 101
  have eq637 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = (X1 ◇ ((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X1)) := superpose eq15 eq101 -- superposition 101,15, 15 into 101, unify on (0).2 in 15 and (0).2 in 101
  have eq743 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq140 eq637 -- forward demodulation 637,140
  have eq1173 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (X0 ◇ sK2)) := superpose eq630 eq17 -- superposition 17,630, 630 into 17, unify on (0).2 in 630 and (0).2 in 17
  have eq1508 (X1 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (X1 ◇ (sK2 ◇ X1))) := superpose eq9 eq1173 -- superposition 1173,9, 9 into 1173, unify on (0).2 in 9 and (0).2.2 in 1173
  subsumption eq1508 eq743


@[equational_result]
theorem Equation4453_implies_Equation4449 (G : Type*) [Magma G] (h : Equation4453 G) : Equation4449 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X1) = ((X3 ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = ((X1 ◇ (X2 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq34 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((X0 ◇ sK2) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq66 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) = ((X2 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2.1.2 in 15
  have eq73 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = ((X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2.1 in 15
  have eq74 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = ((X3 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).2 in 15
  have eq77 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) = ((X3 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq95 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3) := superpose eq74 eq73 -- backward demodulation 73,74
  have eq98 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) = (X1 ◇ (X3 ◇ X1)) := superpose eq74 eq66 -- backward demodulation 66,74
  have eq100 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) = (X0 ◇ (X2 ◇ X0)) := superpose eq74 eq77 -- forward demodulation 77,74
  have eq101 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq74 eq100 -- forward demodulation 100,74
  have eq206 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X2) = (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq270 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq98 eq206 -- forward demodulation 206,98
  have eq501 (X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (((X1 ◇ sK2) ◇ ((X2 ◇ sK2) ◇ X1)) ◇ sK1) := superpose eq11 eq34 -- superposition 34,11, 11 into 34, unify on (0).2 in 11 and (0).2.1 in 34
  have eq563 (X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ (((X2 ◇ sK2) ◇ X1) ◇ sK2)) ◇ sK1) := superpose eq9 eq501 -- forward demodulation 501,9
  have eq564 (X1 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ ((sK2 ◇ (X1 ◇ sK2)) ◇ sK2)) ◇ sK1) := superpose eq9 eq563 -- forward demodulation 563,9
  have eq565 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) ◇ sK1) := superpose eq270 eq564 -- forward demodulation 564,270
  have eq606 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1)))) := superpose eq101 eq101 -- superposition 101,101, 101 into 101, unify on (0).2 in 101 and (0).2.2.2 in 101
  have eq723 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) = ((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq270 eq606 -- forward demodulation 606,270
  have eq724 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq270 eq723 -- forward demodulation 723,270
  have eq725 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ sK1) := superpose eq724 eq565 -- backward demodulation 565,724
  subsumption eq725 eq95


@[equational_result]
theorem Equation4453_implies_Equation4465 (G : Type*) [Magma G] (h : Equation4453 G) : Equation4465 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK3) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X1) = ((X3 ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = ((X1 ◇ (X2 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq34 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((X0 ◇ sK3) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq66 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) = ((X2 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2.1.2 in 15
  have eq73 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = ((X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2.1 in 15
  have eq74 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = ((X3 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).2 in 15
  have eq77 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) = ((X3 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq95 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3) := superpose eq74 eq73 -- backward demodulation 73,74
  have eq98 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) = (X1 ◇ (X3 ◇ X1)) := superpose eq74 eq66 -- backward demodulation 66,74
  have eq100 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) = (X0 ◇ (X2 ◇ X0)) := superpose eq74 eq77 -- forward demodulation 77,74
  have eq101 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq74 eq100 -- forward demodulation 100,74
  have eq206 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X2) = (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq270 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq98 eq206 -- forward demodulation 206,98
  have eq501 (X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (((X1 ◇ sK3) ◇ ((X2 ◇ sK3) ◇ X1)) ◇ sK1) := superpose eq11 eq34 -- superposition 34,11, 11 into 34, unify on (0).2 in 11 and (0).2.1 in 34
  have eq563 (X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK3 ◇ (((X2 ◇ sK3) ◇ X1) ◇ sK3)) ◇ sK1) := superpose eq9 eq501 -- forward demodulation 501,9
  have eq564 (X1 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK3 ◇ ((sK3 ◇ (X1 ◇ sK3)) ◇ sK3)) ◇ sK1) := superpose eq9 eq563 -- forward demodulation 563,9
  have eq565 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK3 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ sK3)))) ◇ sK1) := superpose eq270 eq564 -- forward demodulation 564,270
  have eq606 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1)))) := superpose eq101 eq101 -- superposition 101,101, 101 into 101, unify on (0).2 in 101 and (0).2.2.2 in 101
  have eq723 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) = ((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq270 eq606 -- forward demodulation 606,270
  have eq724 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq270 eq723 -- forward demodulation 723,270
  have eq725 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK3 ◇ (sK3 ◇ (sK3 ◇ sK3))) ◇ sK1) := superpose eq724 eq565 -- backward demodulation 565,724
  subsumption eq725 eq95


@[equational_result]
theorem Equation4453_implies_Equation4457 (G : Type*) [Magma G] (h : Equation4453 G) : Equation4457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X1) = ((X3 ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = ((X1 ◇ (X2 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq38 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((X0 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq66 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) = ((X2 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2.1.2 in 15
  have eq73 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = ((X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2.1 in 15
  have eq74 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = ((X3 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).2 in 15
  have eq77 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) = ((X3 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq95 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3) := superpose eq74 eq73 -- backward demodulation 73,74
  have eq98 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) = (X1 ◇ (X3 ◇ X1)) := superpose eq74 eq66 -- backward demodulation 66,74
  have eq100 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) = (X0 ◇ (X2 ◇ X0)) := superpose eq74 eq77 -- forward demodulation 77,74
  have eq101 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq74 eq100 -- forward demodulation 100,74
  have eq206 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X2) = (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq270 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq98 eq206 -- forward demodulation 206,98
  have eq501 (X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (((X1 ◇ sK1) ◇ ((X2 ◇ sK1) ◇ X1)) ◇ sK1) := superpose eq11 eq38 -- superposition 38,11, 11 into 38, unify on (0).2 in 11 and (0).2.1 in 38
  have eq563 (X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ (((X2 ◇ sK1) ◇ X1) ◇ sK1)) ◇ sK1) := superpose eq9 eq501 -- forward demodulation 501,9
  have eq564 (X1 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ ((sK1 ◇ (X1 ◇ sK1)) ◇ sK1)) ◇ sK1) := superpose eq9 eq563 -- forward demodulation 563,9
  have eq565 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK1) := superpose eq270 eq564 -- forward demodulation 564,270
  have eq606 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1)))) := superpose eq101 eq101 -- superposition 101,101, 101 into 101, unify on (0).2 in 101 and (0).2.2.2 in 101
  have eq723 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) = ((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq270 eq606 -- forward demodulation 606,270
  have eq724 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq270 eq723 -- forward demodulation 723,270
  have eq725 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1) := superpose eq724 eq565 -- backward demodulation 565,724
  subsumption eq725 eq95


@[equational_result]
theorem Equation4453_implies_Equation4439 (G : Type*) [Magma G] (h : Equation4453 G) : Equation4439 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X1) = ((X3 ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = ((X1 ◇ (X2 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq34 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((X0 ◇ sK2) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq66 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) = ((X2 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2.1.2 in 15
  have eq73 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = ((X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2.1 in 15
  have eq74 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = ((X3 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).2 in 15
  have eq77 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) = ((X3 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq95 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3) := superpose eq74 eq73 -- backward demodulation 73,74
  have eq98 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) = (X1 ◇ (X3 ◇ X1)) := superpose eq74 eq66 -- backward demodulation 66,74
  have eq100 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) = (X0 ◇ (X2 ◇ X0)) := superpose eq74 eq77 -- forward demodulation 77,74
  have eq101 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq74 eq100 -- forward demodulation 100,74
  have eq206 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X2) = (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq270 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq98 eq206 -- forward demodulation 206,98
  have eq501 (X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (((X1 ◇ sK2) ◇ ((X2 ◇ sK2) ◇ X1)) ◇ sK1) := superpose eq11 eq34 -- superposition 34,11, 11 into 34, unify on (0).2 in 11 and (0).2.1 in 34
  have eq563 (X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ (((X2 ◇ sK2) ◇ X1) ◇ sK2)) ◇ sK1) := superpose eq9 eq501 -- forward demodulation 501,9
  have eq564 (X1 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ ((sK2 ◇ (X1 ◇ sK2)) ◇ sK2)) ◇ sK1) := superpose eq9 eq563 -- forward demodulation 563,9
  have eq565 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) ◇ sK1) := superpose eq270 eq564 -- forward demodulation 564,270
  have eq606 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1)))) := superpose eq101 eq101 -- superposition 101,101, 101 into 101, unify on (0).2 in 101 and (0).2.2.2 in 101
  have eq723 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) = ((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq270 eq606 -- forward demodulation 606,270
  have eq724 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq270 eq723 -- forward demodulation 723,270
  have eq725 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ sK1) := superpose eq724 eq565 -- backward demodulation 565,724
  subsumption eq725 eq95


@[equational_result]
theorem Equation1051_implies_Equation107 (G : Type*) [Magma G] (h : Equation1051 G) : Equation107 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation72_implies_Equation703 (G : Type*) [Magma G] (h : Equation72 G) : Equation703 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq12 eq9


@[equational_result]
theorem Equation72_implies_Equation55 (G : Type*) [Magma G] (h : Equation72 G) : Equation55 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq14 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq15 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).1.2 in 14
  have eq56 : sK0 ≠ sK0 := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2 in 10
  subsumption eq56 rfl


@[equational_result]
theorem Equation72_implies_Equation909 (G : Type*) [Magma G] (h : Equation72 G) : Equation909 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).1.2.2 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1.2 in 25
  have eq192 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) := superpose eq15 eq39 -- superposition 39,15, 15 into 39, unify on (0).2 in 15 and (0).2.2.2.2 in 39
  have eq253 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq57 eq192 -- forward demodulation 192,57
  have eq254 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq253 eq10 -- backward demodulation 10,253
  subsumption eq254 eq9


@[equational_result]
theorem Equation1845_implies_Equation2246 (G : Type*) [Magma G] (h : Equation1845 G) : Equation2246 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq29 (X0 : G) : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1.2 in 10
  have eq30 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq9 eq13 -- forward demodulation 13,9
  subsumption eq29 eq30


@[equational_result]
theorem Equation1845_implies_Equation4288 (G : Type*) [Magma G] (h : Equation1845 G) : Equation4288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq21 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2 in 12
  have eq28 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq28 eq21


@[equational_result]
theorem Equation1845_implies_Equation2249 (G : Type*) [Magma G] (h : Equation1845 G) : Equation2249 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq25 (X0 : G) : sK0 ≠ ((sK0 ◇ (X0 ◇ X0)) ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  have eq29 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq32 (X1 : G) : sK0 ≠ ((sK0 ◇ (sK0 ◇ X1)) ◇ sK0) := superpose eq12 eq25 -- superposition 25,12, 12 into 25, unify on (0).2 in 12 and (0).2.1 in 25
  subsumption eq32 eq29


@[equational_result]
theorem Equation1845_implies_Equation2243 (G : Type*) [Magma G] (h : Equation1845 G) : Equation2243 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq25 (X0 : G) : sK0 ≠ ((sK0 ◇ (X0 ◇ X0)) ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  have eq29 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq32 (X1 : G) : sK0 ≠ ((sK0 ◇ (sK0 ◇ X1)) ◇ sK0) := superpose eq12 eq25 -- superposition 25,12, 12 into 25, unify on (0).2 in 12 and (0).2.1 in 25
  subsumption eq32 eq29


@[equational_result]
theorem Equation1845_implies_Equation4282 (G : Type*) [Magma G] (h : Equation1845 G) : Equation4282 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq22 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 eq12


@[equational_result]
theorem Equation1845_implies_Equation211 (G : Type*) [Magma G] (h : Equation1845 G) : Equation211 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq28 (X0 : G) : sK0 ≠ ((sK0 ◇ (sK0 ◇ X0)) ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  have eq29 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq9 eq13 -- forward demodulation 13,9
  subsumption eq28 eq29


@[equational_result]
theorem Equation3483_implies_Equation3288 (G : Type*) [Magma G] (h : Equation3483 G) : Equation3288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq33 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq33 eq15


@[equational_result]
theorem Equation3483_implies_Equation3268 (G : Type*) [Magma G] (h : Equation3483 G) : Equation3268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq33 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq33 eq15


@[equational_result]
theorem Equation3483_implies_Equation3500 (G : Type*) [Magma G] (h : Equation3483 G) : Equation3500 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X2)) = (X3 ◇ ((X3 ◇ X0) ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq22 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq48 (X1 X2 X3 X4 : G) : (X2 ◇ X2) = (X3 ◇ ((X3 ◇ X1) ◇ X4)) := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1 in 11
  have eq93 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ ((X0 ◇ X0) ◇ sK1)) := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).2.2.1 in 10
  have eq470 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ X4) = (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X5)) := superpose eq48 eq48 -- superposition 48,48, 48 into 48, unify on (0).2 in 48 and (0).2.2.1 in 48
  have eq565 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ sK1)) := superpose eq9 eq93 -- superposition 93,9, 9 into 93, unify on (0).2 in 9 and (0).2.2.1 in 93
  subsumption eq565 eq470


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
theorem Equation3483_implies_Equation3472 (G : Type*) [Magma G] (h : Equation3483 G) : Equation3472 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq22 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq88 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq22 eq9 -- superposition 9,22, 22 into 9, unify on (0).2 in 22 and (0).2.2.1 in 9
  have eq93 (X0 : G) : (X0 ◇ X0) ≠ (sK1 ◇ ((X0 ◇ X0) ◇ sK1)) := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).1 in 10
  subsumption eq93 eq88


@[equational_result]
theorem Equation3483_implies_Equation3458 (G : Type*) [Magma G] (h : Equation3483 G) : Equation3458 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq50 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq50 eq23


@[equational_result]
theorem Equation3483_implies_Equation3278 (G : Type*) [Magma G] (h : Equation3483 G) : Equation3278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq33 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq33 eq15


@[equational_result]
theorem Equation3483_implies_Equation307 (G : Type*) [Magma G] (h : Equation3483 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (X2 ◇ X2)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.2 in 8
  have eq21 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq8 eq14 -- superposition 14,8, 8 into 14, unify on (0).2 in 8 and (0).2 in 14
  have eq28 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2 in 9
  subsumption eq28 eq21


@[equational_result]
theorem Equation3483_implies_Equation3459 (G : Type*) [Magma G] (h : Equation3483 G) : Equation3459 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq50 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq50 eq23


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
theorem Equation3696_implies_Equation3709 (G : Type*) [Magma G] (h : Equation3696 G) : Equation3709 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ (X3 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq20 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X4) ◇ X3)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq69 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ X4) ◇ (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4)) := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).2.2.1 in 12
  have eq70 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X3) = (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X3 ◇ X4) ◇ X0)) := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).2.1 in 12
  have eq71 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.2 in 9
  have eq72 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.1 in 9
  have eq83 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq20 eq69 -- forward demodulation 69,20
  have eq86 (X0 X1 X3 X4 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ ((X3 ◇ X4) ◇ X0)) := superpose eq83 eq70 -- forward demodulation 70,83
  have eq87 (X0 X1 X3 : G) : (X1 ◇ X1) = ((X3 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq83 eq71 -- forward demodulation 71,83
  have eq88 (X0 X1 X3 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ (X3 ◇ X0)) := superpose eq83 eq72 -- forward demodulation 72,83
  have eq107 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq87 eq10 -- superposition 10,87, 87 into 10, unify on (0).2 in 87 and (0).2 in 10
  have eq331 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X2)) = ((X3 ◇ X3) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X2))) := superpose eq88 eq88 -- superposition 88,88, 88 into 88, unify on (0).2 in 88 and (0).2.2 in 88
  have eq404 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq86 eq331 -- forward demodulation 331,86
  have eq625 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq404 -- superposition 404,9, 9 into 404, unify on (0).2 in 9 and (0).2 in 404
  have eq916 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq625 eq107 -- superposition 107,625, 625 into 107, unify on (0).2 in 625 and (0).2 in 107
  subsumption eq916 eq625


@[equational_result]
theorem Equation3696_implies_Equation3661 (G : Type*) [Magma G] (h : Equation3696 G) : Equation3661 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = ((X3 ◇ X4) ◇ (X0 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq31 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq139 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (sK1 ◇ X1)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq398 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X2)) := superpose eq16 eq139 -- superposition 139,16, 16 into 139, unify on (0).2 in 16 and (0).2 in 139
  subsumption eq398 eq31


@[equational_result]
theorem Equation3696_implies_Equation3671 (G : Type*) [Magma G] (h : Equation3696 G) : Equation3671 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = ((X3 ◇ X4) ◇ (X0 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq31 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq139 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (sK2 ◇ X1)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq398 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X2)) := superpose eq16 eq139 -- superposition 139,16, 16 into 139, unify on (0).2 in 16 and (0).2 in 139
  subsumption eq398 eq31


@[equational_result]
theorem Equation3696_implies_Equation3687 (G : Type*) [Magma G] (h : Equation3696 G) : Equation3687 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ (X3 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq20 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X4) ◇ X3)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq72 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ X4) ◇ (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4)) := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).2.2.1 in 12
  have eq73 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X3) = (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X3 ◇ X4) ◇ X0)) := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).2.1 in 12
  have eq75 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.1 in 9
  have eq84 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq20 eq72 -- forward demodulation 72,20
  have eq87 (X0 X1 X3 X4 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ ((X3 ◇ X4) ◇ X0)) := superpose eq84 eq73 -- forward demodulation 73,84
  have eq89 (X0 X1 X3 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ (X3 ◇ X0)) := superpose eq84 eq75 -- forward demodulation 75,84
  have eq228 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X2)) = ((X3 ◇ X3) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X2))) := superpose eq89 eq89 -- superposition 89,89, 89 into 89, unify on (0).2 in 89 and (0).2.2 in 89
  have eq268 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq89 eq10 -- superposition 10,89, 89 into 10, unify on (0).2 in 89 and (0).2 in 10
  have eq289 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq87 eq228 -- forward demodulation 228,87
  have eq630 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq289 -- superposition 289,9, 9 into 289, unify on (0).2 in 9 and (0).2 in 289
  have eq878 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq630 eq268 -- superposition 268,630, 630 into 268, unify on (0).2 in 630 and (0).2 in 268
  subsumption eq878 eq630


@[equational_result]
theorem Equation3696_implies_Equation3660 (G : Type*) [Magma G] (h : Equation3696 G) : Equation3660 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ (X3 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq20 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X4) ◇ X3)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq72 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ X4) ◇ (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4)) := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).2.2.1 in 12
  have eq75 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.1 in 9
  have eq84 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq20 eq72 -- forward demodulation 72,20
  have eq89 (X0 X1 X3 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ (X3 ◇ X0)) := superpose eq84 eq75 -- forward demodulation 75,84
  have eq268 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq89 eq10 -- superposition 10,89, 89 into 10, unify on (0).2 in 89 and (0).2 in 10
  subsumption eq268 rfl


@[equational_result]
theorem Equation3696_implies_Equation3663 (G : Type*) [Magma G] (h : Equation3696 G) : Equation3663 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ (X3 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq20 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X4) ◇ X3)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq69 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ X4) ◇ (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4)) := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).2.2.1 in 12
  have eq70 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X3) = (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X3 ◇ X4) ◇ X0)) := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).2.1 in 12
  have eq72 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.1 in 9
  have eq83 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq20 eq69 -- forward demodulation 69,20
  have eq86 (X0 X1 X3 X4 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ ((X3 ◇ X4) ◇ X0)) := superpose eq83 eq70 -- forward demodulation 70,83
  have eq88 (X0 X1 X3 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ (X3 ◇ X0)) := superpose eq83 eq72 -- forward demodulation 72,83
  have eq228 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X2)) = ((X3 ◇ X3) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X2))) := superpose eq88 eq88 -- superposition 88,88, 88 into 88, unify on (0).2 in 88 and (0).2.2 in 88
  have eq289 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq86 eq228 -- forward demodulation 228,86
  have eq643 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq289 eq10 -- superposition 10,289, 289 into 10, unify on (0).2 in 289 and (0).2 in 10
  subsumption eq643 rfl


@[equational_result]
theorem Equation3696_implies_Equation3690 (G : Type*) [Magma G] (h : Equation3696 G) : Equation3690 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ (X3 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq20 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X4) ◇ X3)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq69 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ X4) ◇ (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4)) := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).2.2.1 in 12
  have eq70 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X3) = (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X3 ◇ X4) ◇ X0)) := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).2.1 in 12
  have eq72 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.1 in 9
  have eq83 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq20 eq69 -- forward demodulation 69,20
  have eq86 (X0 X1 X3 X4 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ ((X3 ◇ X4) ◇ X0)) := superpose eq83 eq70 -- forward demodulation 70,83
  have eq88 (X0 X1 X3 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ (X3 ◇ X0)) := superpose eq83 eq72 -- forward demodulation 72,83
  have eq228 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X2)) = ((X3 ◇ X3) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X2))) := superpose eq88 eq88 -- superposition 88,88, 88 into 88, unify on (0).2 in 88 and (0).2.2 in 88
  have eq289 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq86 eq228 -- forward demodulation 228,86
  have eq630 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq289 -- superposition 289,9, 9 into 289, unify on (0).2 in 9 and (0).2 in 289
  have eq643 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq289 eq10 -- superposition 10,289, 289 into 10, unify on (0).2 in 289 and (0).2 in 10
  subsumption eq643 eq630


@[equational_result]
theorem Equation3696_implies_Equation3680 (G : Type*) [Magma G] (h : Equation3696 G) : Equation3680 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = ((X3 ◇ X4) ◇ (X0 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq31 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq139 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (sK2 ◇ X1)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq398 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X2)) := superpose eq16 eq139 -- superposition 139,16, 16 into 139, unify on (0).2 in 16 and (0).2 in 139
  subsumption eq398 eq31


@[equational_result]
theorem Equation3696_implies_Equation3693 (G : Type*) [Magma G] (h : Equation3696 G) : Equation3693 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ (X3 ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq20 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X4) ◇ X3)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq69 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ X4) ◇ (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4)) := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).2.2.1 in 12
  have eq70 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X3) = (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X3 ◇ X4) ◇ X0)) := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).2.1 in 12
  have eq72 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.1 in 9
  have eq83 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq20 eq69 -- forward demodulation 69,20
  have eq86 (X0 X1 X3 X4 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ ((X3 ◇ X4) ◇ X0)) := superpose eq83 eq70 -- forward demodulation 70,83
  have eq88 (X0 X1 X3 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ (X3 ◇ X0)) := superpose eq83 eq72 -- forward demodulation 72,83
  have eq228 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X2)) = ((X3 ◇ X3) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X2))) := superpose eq88 eq88 -- superposition 88,88, 88 into 88, unify on (0).2 in 88 and (0).2.2 in 88
  have eq289 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq86 eq228 -- forward demodulation 228,86
  have eq630 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq289 -- superposition 289,9, 9 into 289, unify on (0).2 in 9 and (0).2 in 289
  have eq643 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq289 eq10 -- superposition 10,289, 289 into 10, unify on (0).2 in 289 and (0).2 in 10
  subsumption eq643 eq630


@[equational_result]
theorem Equation3696_implies_Equation3708 (G : Type*) [Magma G] (h : Equation3696 G) : Equation3708 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = ((X3 ◇ X4) ◇ (X0 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq31 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq139 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (sK3 ◇ X1)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq398 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X2)) := superpose eq16 eq139 -- superposition 139,16, 16 into 139, unify on (0).2 in 16 and (0).2 in 139
  subsumption eq398 eq31


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
theorem Equation4082_implies_Equation4622 (G : Type*) [Magma G] (h : Equation4082 G) : Equation4622 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq14 : (sK0 ◇ sK0) ≠ ((sK2 ◇ sK2) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq13


@[equational_result]
theorem Equation4082_implies_Equation4075 (G : Type*) [Magma G] (h : Equation4082 G) : Equation4075 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq14 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq63 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq13 -- superposition 13,28, 28 into 13, unify on (0).2 in 28 and (0).2 in 13
  subsumption eq63 eq28


@[equational_result]
theorem Equation4082_implies_Equation3685 (G : Type*) [Magma G] (h : Equation4082 G) : Equation3685 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq39 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq39 eq28


@[equational_result]
theorem Equation4082_implies_Equation3687 (G : Type*) [Magma G] (h : Equation4082 G) : Equation3687 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq35 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq35 eq28


@[equational_result]
theorem Equation4082_implies_Equation3677 (G : Type*) [Magma G] (h : Equation4082 G) : Equation3677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq30 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ X1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq30 eq13


@[equational_result]
theorem Equation4082_implies_Equation40 (G : Type*) [Magma G] (h : Equation4082 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq55 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq10 -- superposition 10,27, 27 into 10, unify on (0).2 in 27 and (0).2 in 10
  subsumption eq55 eq27


@[equational_result]
theorem Equation4082_implies_Equation4109 (G : Type*) [Magma G] (h : Equation4082 G) : Equation4109 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq14 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq63 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq13 -- superposition 13,28, 28 into 13, unify on (0).2 in 28 and (0).2 in 13
  subsumption eq63 eq28


@[equational_result]
theorem Equation4082_implies_Equation4098 (G : Type*) [Magma G] (h : Equation4082 G) : Equation4098 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq14 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq13


@[equational_result]
theorem Equation4082_implies_Equation4108 (G : Type*) [Magma G] (h : Equation4082 G) : Equation4108 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq14 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq63 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq13 -- superposition 13,28, 28 into 13, unify on (0).2 in 28 and (0).2 in 13
  subsumption eq63 eq28


@[equational_result]
theorem Equation4082_implies_Equation4341 (G : Type*) [Magma G] (h : Equation4082 G) : Equation4341 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq62 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq27 eq10 -- superposition 10,27, 27 into 10, unify on (0).2 in 27 and (0).2.2 in 10
  subsumption eq62 rfl


@[equational_result]
theorem Equation4082_implies_Equation4608 (G : Type*) [Magma G] (h : Equation4082 G) : Equation4608 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq14 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq13


@[equational_result]
theorem Equation4082_implies_Equation4110 (G : Type*) [Magma G] (h : Equation4082 G) : Equation4110 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq14 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq63 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq13 -- superposition 13,28, 28 into 13, unify on (0).2 in 28 and (0).2 in 13
  subsumption eq63 eq28


@[equational_result]
theorem Equation4082_implies_Equation4111 (G : Type*) [Magma G] (h : Equation4082 G) : Equation4111 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq14 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq63 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq13 -- superposition 13,28, 28 into 13, unify on (0).2 in 28 and (0).2 in 13
  subsumption eq63 eq28


@[equational_result]
theorem Equation4540_implies_Equation4318 (G : Type*) [Magma G] (h : Equation4540 G) : Equation4318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X3) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X0 ◇ X1))) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq36 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  have eq64 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq81 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK0)) ≠ (sK0 ◇ (X1 ◇ sK2)) := superpose eq15 eq36 -- superposition 36,15, 15 into 36, unify on (0).2 in 15 and (0).1 in 36
  have eq153 (X1 : G) : (sK0 ◇ (X1 ◇ sK2)) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq9 eq81 -- superposition 81,9, 9 into 81, unify on (0).2 in 9 and (0).1 in 81
  have eq373 (X1 X2 : G) : ((sK0 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (sK2 ◇ (X2 ◇ (X1 ◇ sK2)))) := superpose eq14 eq153 -- superposition 153,14, 14 into 153, unify on (0).2 in 14 and (0).1.2 in 153
  subsumption eq373 eq64


@[equational_result]
theorem Equation4540_implies_Equation4282 (G : Type*) [Magma G] (h : Equation4540 G) : Equation4282 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X3) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X0 ◇ X1))) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq32 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  have eq64 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq81 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK1)) ≠ (sK0 ◇ (X1 ◇ sK2)) := superpose eq15 eq32 -- superposition 32,15, 15 into 32, unify on (0).2 in 15 and (0).1 in 32
  have eq153 (X1 : G) : (sK0 ◇ (X1 ◇ sK2)) ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq9 eq81 -- superposition 81,9, 9 into 81, unify on (0).2 in 9 and (0).1 in 81
  have eq373 (X1 X2 : G) : ((sK1 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (sK2 ◇ (X2 ◇ (X1 ◇ sK2)))) := superpose eq14 eq153 -- superposition 153,14, 14 into 153, unify on (0).2 in 14 and (0).1.2 in 153
  subsumption eq373 eq64


@[equational_result]
theorem Equation4540_implies_Equation4361 (G : Type*) [Magma G] (h : Equation4540 G) : Equation4361 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ sK4)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X3) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X0 ◇ X1))) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq36 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK4)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  have eq64 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq81 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK2)) ≠ (sK0 ◇ (X1 ◇ sK4)) := superpose eq15 eq36 -- superposition 36,15, 15 into 36, unify on (0).2 in 15 and (0).1 in 36
  have eq153 (X1 : G) : (sK0 ◇ (X1 ◇ sK4)) ≠ ((sK2 ◇ sK0) ◇ sK0) := superpose eq9 eq81 -- superposition 81,9, 9 into 81, unify on (0).2 in 9 and (0).1 in 81
  have eq373 (X1 X2 : G) : ((sK2 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (sK4 ◇ (X2 ◇ (X1 ◇ sK4)))) := superpose eq14 eq153 -- superposition 153,14, 14 into 153, unify on (0).2 in 14 and (0).1.2 in 153
  subsumption eq373 eq64


@[equational_result]
theorem Equation4540_implies_Equation4357 (G : Type*) [Magma G] (h : Equation4540 G) : Equation4357 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X3) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X0 ◇ X1))) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq36 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK3)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  have eq64 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq81 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK2)) ≠ (sK0 ◇ (X1 ◇ sK3)) := superpose eq15 eq36 -- superposition 36,15, 15 into 36, unify on (0).2 in 15 and (0).1 in 36
  have eq153 (X1 : G) : (sK0 ◇ (X1 ◇ sK3)) ≠ ((sK2 ◇ sK0) ◇ sK0) := superpose eq9 eq81 -- superposition 81,9, 9 into 81, unify on (0).2 in 9 and (0).1 in 81
  have eq373 (X1 X2 : G) : ((sK2 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (sK3 ◇ (X2 ◇ (X1 ◇ sK3)))) := superpose eq14 eq153 -- superposition 153,14, 14 into 153, unify on (0).2 in 14 and (0).1.2 in 153
  subsumption eq373 eq64


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
theorem Equation4540_implies_Equation4385 (G : Type*) [Magma G] (h : Equation4540 G) : Equation4385 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X3) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq36 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK0)) ≠ (sK0 ◇ (X1 ◇ sK1)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1 in 16
  have eq50 (X1 : G) : ((sK0 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (X1 ◇ sK1)) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).1 in 36
  have eq77 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq95 (X0 X1 : G) : ((sK0 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (X1 ◇ X0))) := superpose eq9 eq50 -- superposition 50,9, 9 into 50, unify on (0).2 in 9 and (0).2.2 in 50
  subsumption eq95 eq77


@[equational_result]
theorem Equation4540_implies_Equation4283 (G : Type*) [Magma G] (h : Equation4540 G) : Equation4283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X3) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X0 ◇ X1))) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq36 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  have eq64 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq81 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK1)) ≠ (sK0 ◇ (X1 ◇ sK0)) := superpose eq15 eq36 -- superposition 36,15, 15 into 36, unify on (0).2 in 15 and (0).1 in 36
  have eq153 (X1 : G) : (sK0 ◇ (X1 ◇ sK0)) ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq9 eq81 -- superposition 81,9, 9 into 81, unify on (0).2 in 9 and (0).1 in 81
  have eq373 (X1 X2 : G) : ((sK1 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (X2 ◇ (X1 ◇ sK0)))) := superpose eq14 eq153 -- superposition 153,14, 14 into 153, unify on (0).2 in 14 and (0).1.2 in 153
  subsumption eq373 eq64


@[equational_result]
theorem Equation4540_implies_Equation4666 (G : Type*) [Magma G] (h : Equation4540 G) : Equation4666 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X3) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ (sK1 ◇ (X0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq17 (X0 X1 : G) : (sK1 ◇ (X0 ◇ sK0)) ≠ (sK1 ◇ (X1 ◇ sK2)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1 in 16
  have eq53 (X1 : G) : ((sK2 ◇ sK1) ◇ sK1) ≠ (sK1 ◇ (X1 ◇ sK0)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq76 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq94 (X0 X1 : G) : ((sK2 ◇ sK1) ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (X1 ◇ X0))) := superpose eq9 eq53 -- superposition 53,9, 9 into 53, unify on (0).2 in 9 and (0).2.2 in 53
  subsumption eq94 eq76


@[equational_result]
theorem Equation4540_implies_Equation4442 (G : Type*) [Magma G] (h : Equation4540 G) : Equation4442 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X3) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq36 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK0)) ≠ (sK0 ◇ (X1 ◇ sK1)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1 in 16
  have eq50 (X1 : G) : ((sK0 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (X1 ◇ sK1)) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).1 in 36
  have eq77 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq95 (X0 X1 : G) : ((sK0 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (X1 ◇ X0))) := superpose eq9 eq50 -- superposition 50,9, 9 into 50, unify on (0).2 in 9 and (0).2.2 in 50
  subsumption eq95 eq77


@[equational_result]
theorem Equation4540_implies_Equation4395 (G : Type*) [Magma G] (h : Equation4540 G) : Equation4395 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X3) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq36 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK1)) ≠ (sK0 ◇ (X1 ◇ sK0)) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).1 in 16
  have eq50 (X1 : G) : ((sK1 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (X1 ◇ sK0)) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).1 in 36
  have eq77 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).2 in 12
  have eq95 (X0 X1 : G) : ((sK1 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (X1 ◇ X0))) := superpose eq9 eq50 -- superposition 50,9, 9 into 50, unify on (0).2 in 9 and (0).2.2 in 50
  subsumption eq95 eq77


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
theorem Equation4444_implies_Equation4439 (G : Type*) [Magma G] (h : Equation4444 G) : Equation4439 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq30 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK2) ◇ X0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq107 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq115 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq17 eq30 -- superposition 30,17, 17 into 30, unify on (0).2 in 17 and (0).2 in 30
  subsumption eq115 eq107


@[equational_result]
theorem Equation4444_implies_Equation4446 (G : Type*) [Magma G] (h : Equation4444 G) : Equation4446 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq33 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ X0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq107 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq112 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq17 eq33 -- superposition 33,17, 17 into 33, unify on (0).2 in 17 and (0).2 in 33
  subsumption eq112 eq107


@[equational_result]
theorem Equation4444_implies_Equation4394 (G : Type*) [Magma G] (h : Equation4444 G) : Equation4394 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK2) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq30 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK2) ◇ X0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq107 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq115 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq17 eq30 -- superposition 30,17, 17 into 30, unify on (0).2 in 17 and (0).2 in 30
  subsumption eq115 eq107


@[equational_result]
theorem Equation4444_implies_Equation4457 (G : Type*) [Magma G] (h : Equation4444 G) : Equation4457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq33 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK1) ◇ X0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq107 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq112 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq17 eq33 -- superposition 33,17, 17 into 33, unify on (0).2 in 17 and (0).2 in 33
  subsumption eq112 eq107


@[equational_result]
theorem Equation4444_implies_Equation4465 (G : Type*) [Magma G] (h : Equation4444 G) : Equation4465 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK3) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq30 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK3) ◇ X0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq107 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq115 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq17 eq30 -- superposition 30,17, 17 into 30, unify on (0).2 in 17 and (0).2 in 30
  subsumption eq115 eq107


@[equational_result]
theorem Equation4444_implies_Equation4434 (G : Type*) [Magma G] (h : Equation4444 G) : Equation4434 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq101 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq241 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq101 eq11 -- superposition 11,101, 101 into 11, unify on (0).2 in 101 and (0).1 in 11
  subsumption eq241 eq101


@[equational_result]
theorem Equation4444_implies_Equation4449 (G : Type*) [Magma G] (h : Equation4444 G) : Equation4449 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq30 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK2) ◇ X0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq107 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq115 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq17 eq30 -- superposition 30,17, 17 into 30, unify on (0).2 in 17 and (0).2 in 30
  subsumption eq115 eq107


@[equational_result]
theorem Equation603_implies_Equation436 (G : Type*) [Magma G] (h : Equation603 G) : Equation436 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq12 (X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ X2)) = (X3 ◇ (X4 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X0 ◇ (X2 ◇ X1)))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2.2 in 9
  have eq56 (X0 X1 : G) : sK0 ≠ (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq56 eq24


@[equational_result]
theorem Equation603_implies_Equation4675 (G : Type*) [Magma G] (h : Equation603 G) : Equation4675 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ ((X0 ◇ sK3) ◇ sK2) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation1034_implies_Equation829 (G : Type*) [Magma G] (h : Equation1034 G) : Equation829 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X4 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq25 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq25 rfl


@[equational_result]
theorem Equation1034_implies_Equation831 (G : Type*) [Magma G] (h : Equation1034 G) : Equation831 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X4 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq29 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation1034_implies_Equation3458 (G : Type*) [Magma G] (h : Equation1034 G) : Equation3458 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X4 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X4 : G) : (X0 ◇ (X0 ◇ X4)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq24 : sK0 ≠ sK0 := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  subsumption eq24 rfl


@[equational_result]
theorem Equation269_implies_Equation3262 (G : Type*) [Magma G] (h : Equation269 G) : Equation3262 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X0 ◇ X1) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq22 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 eq12


@[equational_result]
theorem Equation269_implies_Equation4318 (G : Type*) [Magma G] (h : Equation269 G) : Equation4318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X0 ◇ X1) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ X0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 eq12


@[equational_result]
theorem Equation269_implies_Equation4284 (G : Type*) [Magma G] (h : Equation269 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X0 ◇ X1) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq22 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ X0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 eq12


@[equational_result]
theorem Equation269_implies_Equation307 (G : Type*) [Magma G] (h : Equation269 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (X0 ◇ X1) = (X0 ◇ X4) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq18 (X0 : G) : (sK0 ◇ X0) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1 in 9
  subsumption eq18 eq11


@[equational_result]
theorem Equation269_implies_Equation3535 (G : Type*) [Magma G] (h : Equation269 G) : Equation3535 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK1) ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X0 ◇ X1) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq22 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK1) ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq22 eq12


@[equational_result]
theorem Equation1253_implies_Equation108 (G : Type*) [Magma G] (h : Equation1253 G) : Equation108 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation3113_implies_Equation4065 (G : Type*) [Magma G] (h : Equation3113 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.1 in 8
  have eq13 (X0 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1.1.2 in 10
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq13 -- forward demodulation 13,8
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq16 eq9 -- backward demodulation 9,16
  subsumption eq17 rfl


@[equational_result]
theorem Equation3113_implies_Equation4118 (G : Type*) [Magma G] (h : Equation3113 G) : Equation4118 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq14 (X0 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq17 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq14 -- forward demodulation 14,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- backward demodulation 10,17
  subsumption eq18 rfl


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
theorem Equation3113_implies_Equation1629 (G : Type*) [Magma G] (h : Equation3113 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.1 in 8
  have eq13 (X0 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1.1.2 in 10
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq13 -- forward demodulation 13,8
  have eq17 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq16 eq9 -- backward demodulation 9,16
  subsumption eq17 eq16


@[equational_result]
theorem Equation3113_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3113 G) : Equation3456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.1 in 8
  have eq13 (X0 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1.1.2 in 10
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq13 -- forward demodulation 13,8
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq16 eq9 -- backward demodulation 9,16
  subsumption eq17 rfl


@[equational_result]
theorem Equation3113_implies_Equation2441 (G : Type*) [Magma G] (h : Equation3113 G) : Equation2441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.1 in 8
  have eq13 (X0 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1.1.2 in 10
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq13 -- forward demodulation 13,8
  have eq17 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq16 eq9 -- backward demodulation 9,16
  subsumption eq17 eq16


@[equational_result]
theorem Equation4523_implies_Equation4358 (G : Type*) [Magma G] (h : Equation4523 G) : Equation4358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X3) = (X3 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X3)) = ((X1 ◇ (X0 ◇ X2)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq36 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  have eq62 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq83 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK0) ◇ sK0) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).2 in 36
  have eq124 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ X0) = (((X2 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) ◇ X0) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2 in 12
  have eq154 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ X0) = ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) := superpose eq9 eq124 -- forward demodulation 124,9
  have eq155 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X0) = (((X2 ◇ X3) ◇ X0) ◇ X0) := superpose eq62 eq154 -- forward demodulation 154,62
  have eq185 (X0 X1 X3 : G) : ((X0 ◇ (X1 ◇ X3)) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1 in 14
  have eq245 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X3)) ◇ X0) := superpose eq155 eq185 -- forward demodulation 185,155
  have eq246 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq245 eq14 -- backward demodulation 14,245
  have eq344 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq11 eq246 -- superposition 246,11, 11 into 246, unify on (0).2 in 11 and (0).2 in 246
  have eq507 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ X1) := superpose eq9 eq344 -- superposition 344,9, 9 into 344, unify on (0).2 in 9 and (0).1 in 344
  have eq530 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq344 eq83 -- superposition 83,344, 344 into 83, unify on (0).2 in 344 and (0).2 in 83
  subsumption eq530 eq507


@[equational_result]
theorem Equation4523_implies_Equation4284 (G : Type*) [Magma G] (h : Equation4523 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X3) = (X3 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X3)) = ((X1 ◇ (X0 ◇ X2)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq36 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  have eq62 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq83 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).2 in 36
  have eq124 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ X0) = (((X2 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) ◇ X0) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2 in 12
  have eq154 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ X0) = ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) := superpose eq9 eq124 -- forward demodulation 124,9
  have eq155 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X0) = (((X2 ◇ X3) ◇ X0) ◇ X0) := superpose eq62 eq154 -- forward demodulation 154,62
  have eq185 (X0 X1 X3 : G) : ((X0 ◇ (X1 ◇ X3)) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1 in 14
  have eq245 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X3)) ◇ X0) := superpose eq155 eq185 -- forward demodulation 185,155
  have eq246 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq245 eq14 -- backward demodulation 14,245
  have eq344 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq11 eq246 -- superposition 246,11, 11 into 246, unify on (0).2 in 11 and (0).2 in 246
  have eq517 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X0) := superpose eq9 eq344 -- superposition 344,9, 9 into 344, unify on (0).2 in 9 and (0).2 in 344
  have eq530 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq344 eq83 -- superposition 83,344, 344 into 83, unify on (0).2 in 344 and (0).2 in 83
  subsumption eq530 eq517


@[equational_result]
theorem Equation4523_implies_Equation4288 (G : Type*) [Magma G] (h : Equation4523 G) : Equation4288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X3) = (X3 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X3)) = ((X1 ◇ (X0 ◇ X2)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq36 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  have eq62 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq83 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK0) ◇ sK0) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).2 in 36
  have eq124 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ X0) = (((X2 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) ◇ X0) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2 in 12
  have eq154 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ X0) = ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) := superpose eq9 eq124 -- forward demodulation 124,9
  have eq155 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X0) = (((X2 ◇ X3) ◇ X0) ◇ X0) := superpose eq62 eq154 -- forward demodulation 154,62
  have eq185 (X0 X1 X3 : G) : ((X0 ◇ (X1 ◇ X3)) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1 in 14
  have eq245 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X3)) ◇ X0) := superpose eq155 eq185 -- forward demodulation 185,155
  have eq246 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq245 eq14 -- backward demodulation 14,245
  have eq344 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq11 eq246 -- superposition 246,11, 11 into 246, unify on (0).2 in 11 and (0).2 in 246
  have eq517 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X0) := superpose eq9 eq344 -- superposition 344,9, 9 into 344, unify on (0).2 in 9 and (0).2 in 344
  have eq530 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq344 eq83 -- superposition 83,344, 344 into 83, unify on (0).2 in 344 and (0).2 in 83
  subsumption eq530 eq517


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
theorem Equation4523_implies_Equation4405 (G : Type*) [Magma G] (h : Equation4523 G) : Equation4405 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK1 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
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
  have eq525 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X0) := superpose eq9 eq352 -- superposition 352,9, 9 into 352, unify on (0).2 in 9 and (0).2 in 352
  have eq551 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq352 eq10 -- superposition 10,352, 352 into 10, unify on (0).2 in 352 and (0).1 in 10
  subsumption eq551 eq525


@[equational_result]
theorem Equation4523_implies_Equation4286 (G : Type*) [Magma G] (h : Equation4523 G) : Equation4286 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X3) = (X3 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X3)) = ((X1 ◇ (X0 ◇ X2)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq36 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  have eq62 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq83 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK0) ◇ sK0) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).2 in 36
  have eq124 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ X0) = (((X2 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) ◇ X0) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2 in 12
  have eq154 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ X0) = ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) := superpose eq9 eq124 -- forward demodulation 124,9
  have eq155 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X0) = (((X2 ◇ X3) ◇ X0) ◇ X0) := superpose eq62 eq154 -- forward demodulation 154,62
  have eq185 (X0 X1 X3 : G) : ((X0 ◇ (X1 ◇ X3)) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1 in 14
  have eq245 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X3)) ◇ X0) := superpose eq155 eq185 -- forward demodulation 185,155
  have eq246 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq245 eq14 -- backward demodulation 14,245
  have eq344 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq11 eq246 -- superposition 246,11, 11 into 246, unify on (0).2 in 11 and (0).2 in 246
  have eq517 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X0) := superpose eq9 eq344 -- superposition 344,9, 9 into 344, unify on (0).2 in 9 and (0).2 in 344
  have eq530 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq344 eq83 -- superposition 83,344, 344 into 83, unify on (0).2 in 344 and (0).2 in 83
  subsumption eq530 eq517


@[equational_result]
theorem Equation1289_implies_Equation2238 (G : Type*) [Magma G] (h : Equation1289 G) : Equation2238 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq15 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq18 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1 in 8
  have eq20 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1.1 in 8
  have eq22 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq18 eq15 -- backward demodulation 15,18
  have eq24 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq18 eq20 -- forward demodulation 20,18
  have eq26 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose eq24 eq22 -- backward demodulation 22,24
  have eq27 : sK0 ≠ sK0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).2 in 9
  subsumption eq27 rfl


@[equational_result]
theorem Equation1289_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1289 G) : Equation1020 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq15 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq18 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1 in 8
  have eq20 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1.1 in 8
  have eq24 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq18 eq20 -- forward demodulation 20,18
  have eq27 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq24 eq9 -- backward demodulation 9,24
  have eq32 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq18 eq8 -- superposition 8,18, 18 into 8, unify on (0).2 in 18 and (0).1.2.1 in 8
  have eq36 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq24 eq32 -- forward demodulation 32,24
  have eq62 : sK0 ≠ sK0 := superpose eq36 eq27 -- superposition 27,36, 36 into 27, unify on (0).2 in 36 and (0).2 in 27
  subsumption eq62 rfl


@[equational_result]
theorem Equation1289_implies_Equation614 (G : Type*) [Magma G] (h : Equation1289 G) : Equation614 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq15 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq18 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1 in 8
  have eq20 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1.1 in 8
  have eq23 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq18 eq9 -- backward demodulation 9,18
  have eq25 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq18 eq20 -- forward demodulation 20,18
  have eq32 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq18 eq8 -- superposition 8,18, 18 into 8, unify on (0).2 in 18 and (0).1.2.1 in 8
  have eq36 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq25 eq32 -- forward demodulation 32,25
  have eq59 : sK0 ≠ sK0 := superpose eq36 eq23 -- superposition 23,36, 36 into 23, unify on (0).2 in 36 and (0).2 in 23
  subsumption eq59 rfl


@[equational_result]
theorem Equation1289_implies_Equation4380 (G : Type*) [Magma G] (h : Equation1289 G) : Equation4380 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq15 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq18 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1 in 8
  have eq46 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).2 in 9
  subsumption eq46 rfl


@[equational_result]
theorem Equation1289_implies_Equation3050 (G : Type*) [Magma G] (h : Equation1289 G) : Equation3050 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq15 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq21 : sK0 ≠ sK0 := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).2 in 9
  subsumption eq21 rfl


@[equational_result]
theorem Equation1289_implies_Equation2847 (G : Type*) [Magma G] (h : Equation1289 G) : Equation2847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq15 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq18 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1 in 8
  have eq20 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1.1 in 8
  have eq22 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq18 eq15 -- backward demodulation 15,18
  have eq24 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq18 eq20 -- forward demodulation 20,18
  have eq26 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose eq24 eq22 -- backward demodulation 22,24
  have eq27 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := superpose eq24 eq9 -- backward demodulation 9,24
  subsumption eq27 eq26


@[equational_result]
theorem Equation1289_implies_Equation2441 (G : Type*) [Magma G] (h : Equation1289 G) : Equation2441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq15 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq18 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1 in 8
  have eq20 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1.1 in 8
  have eq22 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq18 eq15 -- backward demodulation 15,18
  have eq23 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := superpose eq18 eq9 -- backward demodulation 9,18
  have eq25 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq18 eq20 -- forward demodulation 20,18
  have eq27 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose eq25 eq22 -- backward demodulation 22,25
  have eq30 : sK0 ≠ sK0 := superpose eq27 eq23 -- superposition 23,27, 27 into 23, unify on (0).2 in 27 and (0).2 in 23
  subsumption eq30 rfl


@[equational_result]
theorem Equation1289_implies_Equation411 (G : Type*) [Magma G] (h : Equation1289 G) : Equation411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq10 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq15 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq18 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1 in 8
  have eq20 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1.1 in 8
  have eq24 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq18 eq20 -- forward demodulation 20,18
  have eq42 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq18 eq8 -- superposition 8,18, 18 into 8, unify on (0).2 in 18 and (0).1.2.1 in 8
  have eq48 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq24 eq42 -- forward demodulation 42,24
  have eq79 : sK0 ≠ sK0 := superpose eq48 eq9 -- superposition 9,48, 48 into 9, unify on (0).2 in 48 and (0).2 in 9
  subsumption eq79 rfl


@[equational_result]
theorem Equation2076_implies_Equation2038 (G : Type*) [Magma G] (h : Equation2076 G) : Equation2038 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2.2 in 12
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq29 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X3) ◇ X1)) = ((X4 ◇ X5) ◇ (((X0 ◇ X2) ◇ X3) ◇ X5)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.1 in 11
  have eq30 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X2) = ((X3 ◇ (X1 ◇ X2)) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq43 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X3) ◇ X1)) = ((X4 ◇ (X0 ◇ X2)) ◇ X3) := superpose eq11 eq29 -- forward demodulation 29,11
  have eq169 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).2.2 in 11
  have eq213 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) ◇ X2) ◇ X3) = X0 := superpose eq11 eq33 -- superposition 33,11, 11 into 33, unify on (0).2 in 11 and (0).1 in 33
  have eq235 (X0 X1 X2 X3 : G) : (((X0 ◇ (X2 ◇ X1)) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X3) = X0 := superpose eq30 eq213 -- forward demodulation 213,30
  have eq236 (X0 X2 X3 : G) : (((X0 ◇ (X2 ◇ X2)) ◇ X3) ◇ X3) = X0 := superpose eq43 eq235 -- forward demodulation 235,43
  have eq336 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1))) := superpose eq17 eq14 -- superposition 14,17, 17 into 14, unify on (0).2 in 17 and (0).2.2 in 14
  have eq429 (X0 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ ((X2 ◇ X2) ◇ X0)) := superpose eq169 eq336 -- forward demodulation 336,169
  have eq872 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq236 -- superposition 236,9, 9 into 236, unify on (0).2 in 9 and (0).1.1.1 in 236
  have eq1194 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X2)) = X0 := superpose eq429 eq17 -- superposition 17,429, 429 into 17, unify on (0).2 in 429 and (0).1.1 in 17
  have eq4589 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ X0) ◇ (sK1 ◇ sK1)) := superpose eq872 eq10 -- superposition 10,872, 872 into 10, unify on (0).2 in 872 and (0).2.1 in 10
  subsumption eq4589 eq1194


@[equational_result]
theorem Equation2076_implies_Equation3459 (G : Type*) [Magma G] (h : Equation2076 G) : Equation3459 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq159 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq17 eq16 -- superposition 16,17, 17 into 16, unify on (0).2 in 17 and (0).2.2 in 16
  have eq488 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq159 eq10 -- superposition 10,159, 159 into 10, unify on (0).2 in 159 and (0).2 in 10
  subsumption eq488 rfl


@[equational_result]
theorem Equation2076_implies_Equation4673 (G : Type*) [Magma G] (h : Equation2076 G) : Equation4673 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq159 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq17 eq16 -- superposition 16,17, 17 into 16, unify on (0).2 in 17 and (0).2.2 in 16
  have eq481 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X2) ◇ X1) := superpose eq11 eq159 -- superposition 159,11, 11 into 159, unify on (0).2 in 11 and (0).2 in 159
  have eq3053 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq481 eq10 -- superposition 10,481, 481 into 10, unify on (0).2 in 481 and (0).2 in 10
  subsumption eq3053 rfl


@[equational_result]
theorem Equation2076_implies_Equation3315 (G : Type*) [Magma G] (h : Equation2076 G) : Equation3315 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq159 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq17 eq16 -- superposition 16,17, 17 into 16, unify on (0).2 in 17 and (0).2.2 in 16
  have eq480 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq33 eq159 -- superposition 159,33, 33 into 159, unify on (0).2 in 33 and (0).2.2 in 159
  have eq2556 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq480 eq10 -- superposition 10,480, 480 into 10, unify on (0).2 in 480 and (0).2 in 10
  subsumption eq2556 rfl


@[equational_result]
theorem Equation2076_implies_Equation2688 (G : Type*) [Magma G] (h : Equation2076 G) : Equation2688 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq30 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X2) = ((X3 ◇ (X1 ◇ X2)) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq1374 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ sK2) := superpose eq30 eq10 -- superposition 10,30, 30 into 10, unify on (0).2 in 30 and (0).2 in 10
  subsumption eq1374 eq17


@[equational_result]
theorem Equation2076_implies_Equation3256 (G : Type*) [Magma G] (h : Equation2076 G) : Equation3256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq159 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq17 eq16 -- superposition 16,17, 17 into 16, unify on (0).2 in 17 and (0).2.2 in 16
  have eq480 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq33 eq159 -- superposition 159,33, 33 into 159, unify on (0).2 in 33 and (0).2.2 in 159
  have eq2556 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq480 eq10 -- superposition 10,480, 480 into 10, unify on (0).2 in 480 and (0).2 in 10
  subsumption eq2556 rfl


@[equational_result]
theorem Equation2076_implies_Equation3261 (G : Type*) [Magma G] (h : Equation2076 G) : Equation3261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq159 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq17 eq16 -- superposition 16,17, 17 into 16, unify on (0).2 in 17 and (0).2.2 in 16
  have eq490 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq159 eq12 -- superposition 12,159, 159 into 12, unify on (0).2 in 159 and (0).2.2 in 12
  have eq644 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := superpose eq490 eq10 -- backward demodulation 10,490
  subsumption eq644 eq12


@[equational_result]
theorem Equation2076_implies_Equation4358 (G : Type*) [Magma G] (h : Equation2076 G) : Equation4358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq159 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq17 eq16 -- superposition 16,17, 17 into 16, unify on (0).2 in 17 and (0).2.2 in 16
  have eq490 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq159 eq12 -- superposition 12,159, 159 into 12, unify on (0).2 in 159 and (0).2.2 in 12
  have eq3858 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq490 eq10 -- superposition 10,490, 490 into 10, unify on (0).2 in 490 and (0).2 in 10
  subsumption eq3858 rfl


@[equational_result]
theorem Equation2076_implies_Equation2060 (G : Type*) [Magma G] (h : Equation2076 G) : Equation2060 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2.2 in 12
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq29 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X3) ◇ X1)) = ((X4 ◇ X5) ◇ (((X0 ◇ X2) ◇ X3) ◇ X5)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.1 in 11
  have eq30 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X2) = ((X3 ◇ (X1 ◇ X2)) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq43 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X3) ◇ X1)) = ((X4 ◇ (X0 ◇ X2)) ◇ X3) := superpose eq11 eq29 -- forward demodulation 29,11
  have eq169 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).2.2 in 11
  have eq213 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) ◇ X2) ◇ X3) = X0 := superpose eq11 eq33 -- superposition 33,11, 11 into 33, unify on (0).2 in 11 and (0).1 in 33
  have eq235 (X0 X1 X2 X3 : G) : (((X0 ◇ (X2 ◇ X1)) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X3) = X0 := superpose eq30 eq213 -- forward demodulation 213,30
  have eq236 (X0 X2 X3 : G) : (((X0 ◇ (X2 ◇ X2)) ◇ X3) ◇ X3) = X0 := superpose eq43 eq235 -- forward demodulation 235,43
  have eq336 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1))) := superpose eq17 eq14 -- superposition 14,17, 17 into 14, unify on (0).2 in 17 and (0).2.2 in 14
  have eq429 (X0 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ ((X2 ◇ X2) ◇ X0)) := superpose eq169 eq336 -- forward demodulation 336,169
  have eq871 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq236 -- superposition 236,9, 9 into 236, unify on (0).2 in 9 and (0).1.1.1 in 236
  have eq1193 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X2)) = X0 := superpose eq429 eq17 -- superposition 17,429, 429 into 17, unify on (0).2 in 429 and (0).1.1 in 17
  have eq4598 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ X0) ◇ (sK0 ◇ sK0)) := superpose eq871 eq10 -- superposition 10,871, 871 into 10, unify on (0).2 in 871 and (0).2.1 in 10
  subsumption eq4598 eq1193


@[equational_result]
theorem Equation2076_implies_Equation3518 (G : Type*) [Magma G] (h : Equation2076 G) : Equation3518 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2.2 in 12
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq169 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).2.2 in 11
  have eq336 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1))) := superpose eq17 eq14 -- superposition 14,17, 17 into 14, unify on (0).2 in 17 and (0).2.2 in 14
  have eq346 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  have eq431 (X0 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ ((X2 ◇ X2) ◇ X0)) := superpose eq169 eq336 -- forward demodulation 336,169
  subsumption eq346 eq431


@[equational_result]
theorem Equation2076_implies_Equation3306 (G : Type*) [Magma G] (h : Equation2076 G) : Equation3306 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X3 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq82 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ (X2 ◇ X1)) ◇ X1) = X0 := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).1.1.1 in 13
  have eq262 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq33 eq82 -- superposition 82,33, 33 into 82, unify on (0).2 in 33 and (0).1.1 in 82
  have eq2170 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq262 eq10 -- superposition 10,262, 262 into 10, unify on (0).2 in 262 and (0).2 in 10
  subsumption eq2170 rfl


@[equational_result]
theorem Equation2076_implies_Equation3526 (G : Type*) [Magma G] (h : Equation2076 G) : Equation3526 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq159 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq17 eq16 -- superposition 16,17, 17 into 16, unify on (0).2 in 17 and (0).2.2 in 16
  have eq488 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq159 eq10 -- superposition 10,159, 159 into 10, unify on (0).2 in 159 and (0).2 in 10
  subsumption eq488 rfl


@[equational_result]
theorem Equation2076_implies_Equation3323 (G : Type*) [Magma G] (h : Equation2076 G) : Equation3323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq159 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq17 eq16 -- superposition 16,17, 17 into 16, unify on (0).2 in 17 and (0).2.2 in 16
  have eq480 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq33 eq159 -- superposition 159,33, 33 into 159, unify on (0).2 in 33 and (0).2.2 in 159
  have eq2556 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq480 eq10 -- superposition 10,480, 480 into 10, unify on (0).2 in 480 and (0).2 in 10
  subsumption eq2556 rfl


@[equational_result]
theorem Equation2076_implies_Equation3334 (G : Type*) [Magma G] (h : Equation2076 G) : Equation3334 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq159 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq17 eq16 -- superposition 16,17, 17 into 16, unify on (0).2 in 17 and (0).2.2 in 16
  have eq490 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq159 eq12 -- superposition 12,159, 159 into 12, unify on (0).2 in 159 and (0).2.2 in 12
  have eq644 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := superpose eq490 eq10 -- backward demodulation 10,490
  subsumption eq644 eq12


@[equational_result]
theorem Equation1374_implies_Equation466 (G : Type*) [Magma G] (h : Equation1374 G) : Equation466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq22 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq26 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq22 eq10 -- backward demodulation 10,22
  subsumption eq26 eq22


@[equational_result]
theorem Equation1374_implies_Equation1312 (G : Type*) [Magma G] (h : Equation1374 G) : Equation1312 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq22 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq27 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq24 eq10 -- backward demodulation 10,24
  subsumption eq27 eq22


@[equational_result]
theorem Equation1374_implies_Equation1654 (G : Type*) [Magma G] (h : Equation1374 G) : Equation1654 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq15 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq92 : sK0 ≠ sK0 := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq92 rfl


@[equational_result]
theorem Equation1374_implies_Equation2090 (G : Type*) [Magma G] (h : Equation1374 G) : Equation2090 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq18 (X0 X1 X2 X3 X4 : G) : ((((X3 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) ◇ X3) ◇ X0) ◇ (X2 ◇ X4)) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq22 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq30 (X0 X2 X3 : G) : (X0 ◇ X3) = (((X2 ◇ X0) ◇ X2) ◇ X3) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1.2 in 12
  have eq53 (X0 X2 X3 X4 : G) : ((((X3 ◇ (X0 ◇ X2)) ◇ X3) ◇ X0) ◇ (X2 ◇ X4)) = X4 := superpose eq30 eq18 -- backward demodulation 18,30
  have eq58 (X0 X2 X4 : G) : (((X0 ◇ X2) ◇ X0) ◇ (X2 ◇ X4)) = X4 := superpose eq30 eq53 -- forward demodulation 53,30
  have eq91 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose eq22 eq15 -- superposition 15,22, 22 into 15, unify on (0).2 in 22 and (0).1.2 in 15
  have eq95 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK1 ◇ sK0)) := superpose eq91 eq10 -- backward demodulation 10,91
  subsumption eq95 eq58


