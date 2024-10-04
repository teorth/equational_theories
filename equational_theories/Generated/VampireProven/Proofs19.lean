import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation688_implies_Equation2707 (G : Type*) [Magma G] (h : Equation688 G) : Equation2707 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ (sK1 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2 in 14
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq30 (X0 : G) : sK0 ≠ (X0 ◇ sK1) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2 in 15
  subsumption eq30 eq19


@[equational_result]
theorem Equation688_implies_Equation256 (G : Type*) [Magma G] (h : Equation688 G) : Equation256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq18 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq25 (X0 : G) : sK0 ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2.1.1 in 10
  subsumption eq25 eq18


@[equational_result]
theorem Equation688_implies_Equation481 (G : Type*) [Magma G] (h : Equation688 G) : Equation481 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ (sK1 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2 in 14
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq30 (X0 : G) : sK0 ≠ (X0 ◇ sK1) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2 in 15
  subsumption eq30 eq19


@[equational_result]
theorem Equation688_implies_Equation1047 (G : Type*) [Magma G] (h : Equation688 G) : Equation1047 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq20 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq21 : sK0 ≠ sK1 := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).2 in 15
  subsumption eq21 eq20


@[equational_result]
theorem Equation688_implies_Equation177 (G : Type*) [Magma G] (h : Equation688 G) : Equation177 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation688_implies_Equation895 (G : Type*) [Magma G] (h : Equation688 G) : Equation895 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ (sK1 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2 in 14
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq30 (X0 : G) : sK0 ≠ (X0 ◇ sK1) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2 in 15
  subsumption eq30 eq19


@[equational_result]
theorem Equation688_implies_Equation2694 (G : Type*) [Magma G] (h : Equation688 G) : Equation2694 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK3)) ◇ sK3) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ (sK2 ◇ sK3) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2 in 14
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq30 (X0 : G) : sK0 ≠ (X0 ◇ sK3) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2 in 15
  subsumption eq30 eq19


@[equational_result]
theorem Equation688_implies_Equation1836 (G : Type*) [Magma G] (h : Equation688 G) : Equation1836 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq20 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq21 : sK0 ≠ sK1 := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).2 in 15
  subsumption eq21 eq20


@[equational_result]
theorem Equation688_implies_Equation125 (G : Type*) [Magma G] (h : Equation688 G) : Equation125 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq20 : sK0 ≠ (sK1 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 eq19


@[equational_result]
theorem Equation688_implies_Equation2497 (G : Type*) [Magma G] (h : Equation688 G) : Equation2497 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2 in 14
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq30 (X0 : G) : sK0 ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2.1 in 15
  subsumption eq30 eq19


@[equational_result]
theorem Equation688_implies_Equation670 (G : Type*) [Magma G] (h : Equation688 G) : Equation670 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation688_implies_Equation2126 (G : Type*) [Magma G] (h : Equation688 G) : Equation2126 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq22 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation688_implies_Equation2531 (G : Type*) [Magma G] (h : Equation688 G) : Equation2531 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2 in 14
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq30 (X0 : G) : sK0 ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2.1 in 15
  subsumption eq30 eq19


@[equational_result]
theorem Equation688_implies_Equation2 (G : Type*) [Magma G] (h : Equation688 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq18 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq21 eq18


@[equational_result]
theorem Equation688_implies_Equation219 (G : Type*) [Magma G] (h : Equation688 G) : Equation219 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2 in 14
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq30 (X0 : G) : sK0 ≠ (X0 ◇ sK1) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2 in 15
  subsumption eq30 eq19


@[equational_result]
theorem Equation688_implies_Equation3113 (G : Type*) [Magma G] (h : Equation688 G) : Equation3113 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq18 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq21 (X0 : G) : sK0 ≠ (((X0 ◇ sK1) ◇ sK0) ◇ sK1) := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2.1.1.1 in 10
  subsumption eq21 eq18


@[equational_result]
theorem Equation688_implies_Equation4212 (G : Type*) [Magma G] (h : Equation688 G) : Equation4212 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq18 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq25 (X0 : G) : (sK0 ◇ sK1) ≠ X0 := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq25 eq16


@[equational_result]
theorem Equation688_implies_Equation1313 (G : Type*) [Magma G] (h : Equation688 G) : Equation1313 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq20 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 eq19


@[equational_result]
theorem Equation688_implies_Equation2504 (G : Type*) [Magma G] (h : Equation688 G) : Equation2504 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2 in 14
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq30 (X0 : G) : sK0 ≠ ((X0 ◇ sK1) ◇ sK1) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2.1 in 15
  subsumption eq30 eq19


@[equational_result]
theorem Equation688_implies_Equation3163 (G : Type*) [Magma G] (h : Equation688 G) : Equation3163 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK2) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq18 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq21 (X0 : G) : sK0 ≠ (((X0 ◇ sK2) ◇ sK1) ◇ sK0) := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2.1.1.1 in 10
  subsumption eq21 eq18


@[equational_result]
theorem Equation688_implies_Equation907 (G : Type*) [Magma G] (h : Equation688 G) : Equation907 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ (sK1 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2 in 14
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq30 (X0 : G) : sK0 ≠ (X0 ◇ sK0) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2 in 15
  subsumption eq30 eq19


@[equational_result]
theorem Equation688_implies_Equation1719 (G : Type*) [Magma G] (h : Equation688 G) : Equation1719 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq22 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 eq19


@[equational_result]
theorem Equation688_implies_Equation1485 (G : Type*) [Magma G] (h : Equation688 G) : Equation1485 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2 in 14
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq30 (X0 : G) : sK0 ≠ ((X0 ◇ sK0) ◇ sK2) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2.1 in 15
  subsumption eq30 eq19


@[equational_result]
theorem Equation688_implies_Equation474 (G : Type*) [Magma G] (h : Equation688 G) : Equation474 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ (sK1 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2 in 14
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq30 (X0 : G) : sK0 ≠ (X0 ◇ sK1) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2 in 15
  subsumption eq30 eq19


@[equational_result]
theorem Equation688_implies_Equation2294 (G : Type*) [Magma G] (h : Equation688 G) : Equation2294 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2 in 14
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq30 (X0 : G) : sK0 ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2.1 in 15
  subsumption eq30 eq19


@[equational_result]
theorem Equation688_implies_Equation1110 (G : Type*) [Magma G] (h : Equation688 G) : Equation1110 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation688_implies_Equation2700 (G : Type*) [Magma G] (h : Equation688 G) : Equation2700 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2 in 14
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq30 (X0 : G) : sK0 ≠ (X0 ◇ sK1) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2 in 15
  subsumption eq30 eq19


@[equational_result]
theorem Equation688_implies_Equation880 (G : Type*) [Magma G] (h : Equation688 G) : Equation880 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ (sK1 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2 in 14
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq30 (X0 : G) : sK0 ≠ (X0 ◇ sK0) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2 in 15
  subsumption eq30 eq19


@[equational_result]
theorem Equation688_implies_Equation3106 (G : Type*) [Magma G] (h : Equation688 G) : Equation3106 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq18 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq25 (X0 : G) : sK0 ≠ (((X0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2.1.1.1 in 10
  subsumption eq25 eq18


@[equational_result]
theorem Equation688_implies_Equation274 (G : Type*) [Magma G] (h : Equation688 G) : Equation274 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq18 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq21 (X0 : G) : (((sK1 ◇ X0) ◇ sK1) ◇ sK1) ≠ X0 := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).1 in 10
  subsumption eq21 eq16


@[equational_result]
theorem Equation688_implies_Equation1279 (G : Type*) [Magma G] (h : Equation688 G) : Equation1279 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq22 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 eq19


@[equational_result]
theorem Equation688_implies_Equation4311 (G : Type*) [Magma G] (h : Equation688 G) : Equation4311 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK3 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ (sK2 ◇ (sK3 ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq20 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq21 : sK0 ≠ sK3 := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).2 in 15
  subsumption eq21 eq20


@[equational_result]
theorem Equation688_implies_Equation1489 (G : Type*) [Magma G] (h : Equation688 G) : Equation1489 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2 in 14
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq30 (X0 : G) : sK0 ≠ ((X0 ◇ sK0) ◇ sK0) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2.1 in 15
  subsumption eq30 eq19


@[equational_result]
theorem Equation688_implies_Equation1480 (G : Type*) [Magma G] (h : Equation688 G) : Equation1480 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2 in 14
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq30 (X0 : G) : sK0 ≠ ((X0 ◇ sK0) ◇ sK0) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2.1 in 15
  subsumption eq30 eq19


@[equational_result]
theorem Equation688_implies_Equation2301 (G : Type*) [Magma G] (h : Equation688 G) : Equation2301 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2 in 14
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq30 (X0 : G) : sK0 ≠ ((X0 ◇ sK1) ◇ sK1) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2.1 in 15
  subsumption eq30 eq19


@[equational_result]
theorem Equation688_implies_Equation2910 (G : Type*) [Magma G] (h : Equation688 G) : Equation2910 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2 in 14
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq30 (X0 : G) : sK0 ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2.1 in 15
  subsumption eq30 eq19


@[equational_result]
theorem Equation688_implies_Equation3140 (G : Type*) [Magma G] (h : Equation688 G) : Equation3140 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq18 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq21 (X0 : G) : sK0 ≠ (((X0 ◇ sK0) ◇ sK0) ◇ sK1) := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2.1.1.1 in 10
  subsumption eq21 eq18


@[equational_result]
theorem Equation688_implies_Equation2091 (G : Type*) [Magma G] (h : Equation688 G) : Equation2091 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2 in 14
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq33 (X0 : G) : sK0 ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq33 eq19


@[equational_result]
theorem Equation688_implies_Equation118 (G : Type*) [Magma G] (h : Equation688 G) : Equation118 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq20 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 eq19


@[equational_result]
theorem Equation688_implies_Equation704 (G : Type*) [Magma G] (h : Equation688 G) : Equation704 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation462_implies_Equation1245 (G : Type*) [Magma G] (h : Equation462 G) : Equation1245 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X5 X6 X7 : G) : (X5 ◇ (X6 ◇ (X7 ◇ X0))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq16 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq16 eq14


@[equational_result]
theorem Equation462_implies_Equation1836 (G : Type*) [Magma G] (h : Equation462 G) : Equation1836 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X5 X6 X7 : G) : (X5 ◇ (X6 ◇ (X7 ◇ X0))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq16 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq16 eq14


@[equational_result]
theorem Equation462_implies_Equation839 (G : Type*) [Magma G] (h : Equation462 G) : Equation839 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X5 X6 X7 : G) : (X5 ◇ (X6 ◇ (X7 ◇ X0))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq16 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq16 eq14


@[equational_result]
theorem Equation462_implies_Equation1235 (G : Type*) [Magma G] (h : Equation462 G) : Equation1235 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X5 X6 X7 : G) : (X5 ◇ (X6 ◇ (X7 ◇ X0))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq15 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq15 eq14


@[equational_result]
theorem Equation462_implies_Equation3915 (G : Type*) [Magma G] (h : Equation462 G) : Equation3915 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X5 X6 X7 : G) : (X5 ◇ (X6 ◇ (X7 ◇ X0))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq15 rfl


@[equational_result]
theorem Equation462_implies_Equation2069 (G : Type*) [Magma G] (h : Equation462 G) : Equation2069 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X5 X6 X7 : G) : (X5 ◇ (X6 ◇ (X7 ◇ X0))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq16 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK3)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq17 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq14 eq16 -- forward demodulation 16,14
  have eq18 : sK0 ≠ (sK0 ◇ sK2) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation462_implies_Equation4522 (G : Type*) [Magma G] (h : Equation462 G) : Equation4522 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK3) ◇ sK4) := mod_symm nh
  have eq11 (X0 X5 X6 X7 : G) : (X5 ◇ (X6 ◇ (X7 ◇ X0))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq16 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK3) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation462_implies_Equation1263 (G : Type*) [Magma G] (h : Equation462 G) : Equation1263 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X5 X6 X7 : G) : (X5 ◇ (X6 ◇ (X7 ◇ X0))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq16 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq16 eq14


@[equational_result]
theorem Equation462_implies_Equation852 (G : Type*) [Magma G] (h : Equation462 G) : Equation852 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X5 X6 X7 : G) : (X5 ◇ (X6 ◇ (X7 ◇ X0))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq16 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq16 eq14


@[equational_result]
theorem Equation462_implies_Equation1236 (G : Type*) [Magma G] (h : Equation462 G) : Equation1236 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X5 X6 X7 : G) : (X5 ◇ (X6 ◇ (X7 ◇ X0))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq15 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq15 eq14


@[equational_result]
theorem Equation462_implies_Equation361 (G : Type*) [Magma G] (h : Equation462 G) : Equation361 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X5 X6 X7 : G) : (X5 ◇ (X6 ◇ (X7 ◇ X0))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq15 rfl


@[equational_result]
theorem Equation462_implies_Equation3667 (G : Type*) [Magma G] (h : Equation462 G) : Equation3667 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X5 X6 X7 : G) : (X5 ◇ (X6 ◇ (X7 ◇ X0))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq17 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation462_implies_Equation1050 (G : Type*) [Magma G] (h : Equation462 G) : Equation1050 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X5 X6 X7 : G) : (X5 ◇ (X6 ◇ (X7 ◇ X0))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq16 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq16 eq14


@[equational_result]
theorem Equation1618_implies_Equation1547 (G : Type*) [Magma G] (h : Equation1618 G) : Equation1547 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ (X4 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq67 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1.2.2 in 11
  have eq73 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq73 eq67


@[equational_result]
theorem Equation1618_implies_Equation676 (G : Type*) [Magma G] (h : Equation1618 G) : Equation676 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ (X4 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq67 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1.2.2 in 11
  have eq76 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ sK0))) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2.2 in 10
  subsumption eq76 eq67


@[equational_result]
theorem Equation3983_implies_Equation4154 (G : Type*) [Magma G] (h : Equation3983 G) : Equation4154 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq25 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq57 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = (((X0 ◇ (X1 ◇ X2)) ◇ X6) ◇ X5) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1.2 in 25
  have eq72 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).2 in 25
  have eq102 (X0 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = ((X6 ◇ X0) ◇ X5) := superpose eq9 eq57 -- forward demodulation 57,9
  have eq116 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq72 eq25 -- backward demodulation 25,72
  have eq119 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq116 eq18 -- backward demodulation 18,116
  have eq127 (X0 X3 X5 X6 : G) : ((X6 ◇ X0) ◇ X5) = (X5 ◇ (X0 ◇ X3)) := superpose eq116 eq102 -- backward demodulation 102,116
  have eq136 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq116 eq10 -- backward demodulation 10,116
  have eq137 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq116 eq119 -- forward demodulation 119,116
  have eq138 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq116 eq137 -- forward demodulation 137,116
  have eq139 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq116 eq138 -- forward demodulation 138,116
  have eq150 (X0 X5 X6 : G) : (X5 ◇ X0) = ((X6 ◇ X0) ◇ X5) := superpose eq139 eq127 -- forward demodulation 127,139
  subsumption eq136 eq150


@[equational_result]
theorem Equation3983_implies_Equation3994 (G : Type*) [Magma G] (h : Equation3983 G) : Equation3994 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq19 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq26 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq46 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = (((X0 ◇ (X1 ◇ X2)) ◇ X6) ◇ X5) := superpose eq9 eq26 -- superposition 26,9, 9 into 26, unify on (0).2 in 9 and (0).1.2 in 26
  have eq61 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq26 -- superposition 26,9, 9 into 26, unify on (0).2 in 9 and (0).2 in 26
  have eq85 (X0 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = ((X6 ◇ X0) ◇ X5) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq99 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq61 eq26 -- backward demodulation 26,61
  have eq101 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq99 eq19 -- backward demodulation 19,99
  have eq108 (X0 X3 X5 X6 : G) : ((X6 ◇ X0) ◇ X5) = (X5 ◇ (X0 ◇ X3)) := superpose eq99 eq85 -- backward demodulation 85,99
  have eq115 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq99 eq101 -- forward demodulation 101,99
  have eq116 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq99 eq115 -- forward demodulation 115,99
  have eq117 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq99 eq116 -- forward demodulation 116,99
  have eq121 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK0) ◇ sK2) := superpose eq117 eq10 -- backward demodulation 10,117
  have eq127 (X0 X5 X6 : G) : (X5 ◇ X0) = ((X6 ◇ X0) ◇ X5) := superpose eq117 eq108 -- forward demodulation 108,117
  have eq147 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq99 eq117 -- superposition 117,99, 99 into 117, unify on (0).2 in 99 and (0).2 in 117
  have eq150 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ X2) := superpose eq99 eq147 -- forward demodulation 147,99
  have eq187 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ X1) := superpose eq99 eq127 -- superposition 127,99, 99 into 127, unify on (0).2 in 99 and (0).2 in 127
  have eq191 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK0) := superpose eq127 eq121 -- superposition 121,127, 127 into 121, unify on (0).2 in 127 and (0).2 in 121
  have eq262 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ X1) := superpose eq127 eq150 -- superposition 150,127, 127 into 150, unify on (0).2 in 127 and (0).1 in 150
  have eq476 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ X0) := superpose eq262 eq191 -- superposition 191,262, 262 into 191, unify on (0).2 in 262 and (0).2 in 191
  subsumption eq476 eq187


@[equational_result]
theorem Equation3983_implies_Equation4440 (G : Type*) [Magma G] (h : Equation3983 G) : Equation4440 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq25 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq45 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = (((X0 ◇ (X1 ◇ X2)) ◇ X6) ◇ X5) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1.2 in 25
  have eq60 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).2 in 25
  have eq83 (X0 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = ((X6 ◇ X0) ◇ X5) := superpose eq9 eq45 -- forward demodulation 45,9
  have eq97 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq60 eq25 -- backward demodulation 25,60
  have eq99 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq97 eq18 -- backward demodulation 18,97
  have eq106 (X0 X3 X5 X6 : G) : ((X6 ◇ X0) ◇ X5) = (X5 ◇ (X0 ◇ X3)) := superpose eq97 eq83 -- backward demodulation 83,97
  have eq113 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ sK0) := superpose eq97 eq10 -- backward demodulation 10,97
  have eq114 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq99 -- forward demodulation 99,97
  have eq115 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq114 -- forward demodulation 114,97
  have eq116 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq115 -- forward demodulation 115,97
  have eq125 (X0 X5 X6 : G) : (X5 ◇ X0) = ((X6 ◇ X0) ◇ X5) := superpose eq116 eq106 -- forward demodulation 106,116
  have eq131 : (sK2 ◇ sK0) ≠ (sK0 ◇ sK1) := superpose eq116 eq113 -- forward demodulation 113,116
  have eq144 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq97 eq116 -- superposition 116,97, 97 into 116, unify on (0).2 in 97 and (0).2 in 116
  have eq147 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq97 eq144 -- forward demodulation 144,97
  have eq178 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ X1) := superpose eq97 eq125 -- superposition 125,97, 97 into 125, unify on (0).2 in 97 and (0).2 in 125
  have eq299 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ X1) := superpose eq125 eq147 -- superposition 147,125, 125 into 147, unify on (0).2 in 125 and (0).2 in 147
  have eq347 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ X0) := superpose eq299 eq131 -- superposition 131,299, 299 into 131, unify on (0).2 in 299 and (0).1 in 131
  subsumption eq347 eq178


@[equational_result]
theorem Equation3983_implies_Equation3270 (G : Type*) [Magma G] (h : Equation3983 G) : Equation3270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq25 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq45 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = (((X0 ◇ (X1 ◇ X2)) ◇ X6) ◇ X5) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1.2 in 25
  have eq60 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).2 in 25
  have eq74 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK0 ◇ X0) ◇ sK1) := superpose eq25 eq10 -- superposition 10,25, 25 into 10, unify on (0).2 in 25 and (0).2 in 10
  have eq84 (X0 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = ((X6 ◇ X0) ◇ X5) := superpose eq9 eq45 -- forward demodulation 45,9
  have eq98 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq60 eq25 -- backward demodulation 25,60
  have eq100 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq98 eq18 -- backward demodulation 18,98
  have eq107 (X0 X3 X5 X6 : G) : ((X6 ◇ X0) ◇ X5) = (X5 ◇ (X0 ◇ X3)) := superpose eq98 eq84 -- backward demodulation 84,98
  have eq114 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq98 eq100 -- forward demodulation 100,98
  have eq115 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq98 eq114 -- forward demodulation 114,98
  have eq116 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq98 eq115 -- forward demodulation 115,98
  have eq126 (X0 X5 X6 : G) : (X5 ◇ X0) = ((X6 ◇ X0) ◇ X5) := superpose eq116 eq107 -- forward demodulation 107,116
  have eq245 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ X1) := superpose eq98 eq126 -- superposition 126,98, 98 into 126, unify on (0).2 in 98 and (0).2 in 126
  have eq268 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ X3) := superpose eq98 eq245 -- superposition 245,98, 98 into 245, unify on (0).2 in 98 and (0).1 in 245
  have eq299 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((sK0 ◇ X0) ◇ X1) := superpose eq245 eq74 -- superposition 74,245, 245 into 74, unify on (0).2 in 245 and (0).2 in 74
  subsumption eq299 eq268


@[equational_result]
theorem Equation3983_implies_Equation4670 (G : Type*) [Magma G] (h : Equation3983 G) : Equation4670 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK2 ◇ sK3) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq25 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq45 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = (((X0 ◇ (X1 ◇ X2)) ◇ X6) ◇ X5) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1.2 in 25
  have eq60 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).2 in 25
  have eq83 (X0 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = ((X6 ◇ X0) ◇ X5) := superpose eq9 eq45 -- forward demodulation 45,9
  have eq97 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq60 eq25 -- backward demodulation 25,60
  have eq99 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq97 eq18 -- backward demodulation 18,97
  have eq106 (X0 X3 X5 X6 : G) : ((X6 ◇ X0) ◇ X5) = (X5 ◇ (X0 ◇ X3)) := superpose eq97 eq83 -- backward demodulation 83,97
  have eq113 : ((sK2 ◇ sK3) ◇ sK3) ≠ (sK1 ◇ sK0) := superpose eq97 eq10 -- backward demodulation 10,97
  have eq114 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq99 -- forward demodulation 99,97
  have eq115 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq114 -- forward demodulation 114,97
  have eq116 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq115 -- forward demodulation 115,97
  have eq125 (X0 X5 X6 : G) : (X5 ◇ X0) = ((X6 ◇ X0) ◇ X5) := superpose eq116 eq106 -- forward demodulation 106,116
  have eq141 : (sK1 ◇ sK0) ≠ (sK3 ◇ sK2) := superpose eq97 eq113 -- superposition 113,97, 97 into 113, unify on (0).2 in 97 and (0).1 in 113
  have eq144 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq97 eq116 -- superposition 116,97, 97 into 116, unify on (0).2 in 97 and (0).2 in 116
  have eq147 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ X2) := superpose eq97 eq144 -- forward demodulation 144,97
  have eq152 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ X1) := superpose eq97 eq125 -- superposition 125,97, 97 into 125, unify on (0).2 in 97 and (0).2 in 125
  have eq274 (X0 : G) : (sK1 ◇ sK0) ≠ (sK3 ◇ X0) := superpose eq152 eq141 -- superposition 141,152, 152 into 141, unify on (0).2 in 152 and (0).2 in 141
  have eq328 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ X1) := superpose eq125 eq147 -- superposition 147,125, 125 into 147, unify on (0).2 in 125 and (0).1 in 147
  have eq442 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq328 eq328 -- superposition 328,328, 328 into 328, unify on (0).2 in 328 and (0).1 in 328
  have eq461 (X0 X1 : G) : (X0 ◇ X1) ≠ (sK1 ◇ sK0) := superpose eq328 eq274 -- superposition 274,328, 328 into 274, unify on (0).2 in 328 and (0).2 in 274
  subsumption eq461 eq442


@[equational_result]
theorem Equation3983_implies_Equation3457 (G : Type*) [Magma G] (h : Equation3983 G) : Equation3457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq25 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq29 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ (X0 ◇ X1)) = (X4 ◇ ((X2 ◇ X3) ◇ (X5 ◇ X6))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq50 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X3 ◇ (X4 ◇ X5)) ◇ X0) = ((X3 ◇ X6) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1 in 25
  have eq52 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X2 ◇ (X3 ◇ X4)) ◇ (X0 ◇ (X5 ◇ X6))) = ((X2 ◇ X7) ◇ (X0 ◇ X1)) := superpose eq25 eq25 -- superposition 25,25, 25 into 25, unify on (0).2 in 25 and (0).1 in 25
  have eq60 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).2 in 25
  have eq84 (X0 X1 X2 X3 X6 : G) : (X0 ◇ X3) = ((X3 ◇ X6) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq50 -- forward demodulation 50,9
  have eq92 (X0 X1 X2 X7 : G) : ((X2 ◇ X7) ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq84 eq52 -- forward demodulation 52,84
  have eq93 (X0 X1 X2 X4 X5 : G) : (X4 ◇ (X0 ◇ X1)) = (X4 ◇ (X5 ◇ X2)) := superpose eq92 eq29 -- backward demodulation 29,92
  have eq97 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq60 eq25 -- backward demodulation 25,60
  have eq99 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq97 eq18 -- backward demodulation 18,97
  have eq113 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq97 eq10 -- backward demodulation 10,97
  have eq114 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq99 -- forward demodulation 99,97
  have eq115 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq114 -- forward demodulation 114,97
  have eq116 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq115 -- forward demodulation 115,97
  have eq156 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ X4)) := superpose eq116 eq93 -- superposition 93,116, 116 into 93, unify on (0).2 in 116 and (0).1 in 93
  have eq169 (X0 X1 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ X1)) := superpose eq93 eq113 -- superposition 113,93, 93 into 113, unify on (0).2 in 93 and (0).2 in 113
  subsumption eq169 eq156


@[equational_result]
theorem Equation3983_implies_Equation3526 (G : Type*) [Magma G] (h : Equation3983 G) : Equation3526 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq25 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq29 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ (X0 ◇ X1)) = (X4 ◇ ((X2 ◇ X3) ◇ (X5 ◇ X6))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq50 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X3 ◇ (X4 ◇ X5)) ◇ X0) = ((X3 ◇ X6) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1 in 25
  have eq52 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X2 ◇ (X3 ◇ X4)) ◇ (X0 ◇ (X5 ◇ X6))) = ((X2 ◇ X7) ◇ (X0 ◇ X1)) := superpose eq25 eq25 -- superposition 25,25, 25 into 25, unify on (0).2 in 25 and (0).1 in 25
  have eq60 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).2 in 25
  have eq84 (X0 X1 X2 X3 X6 : G) : (X0 ◇ X3) = ((X3 ◇ X6) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq50 -- forward demodulation 50,9
  have eq92 (X0 X1 X2 X7 : G) : ((X2 ◇ X7) ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq84 eq52 -- forward demodulation 52,84
  have eq93 (X0 X1 X2 X4 X5 : G) : (X4 ◇ (X0 ◇ X1)) = (X4 ◇ (X5 ◇ X2)) := superpose eq92 eq29 -- backward demodulation 29,92
  have eq97 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq60 eq25 -- backward demodulation 25,60
  have eq99 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq97 eq18 -- backward demodulation 18,97
  have eq113 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK1)) := superpose eq97 eq10 -- backward demodulation 10,97
  have eq114 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq99 -- forward demodulation 99,97
  have eq115 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq114 -- forward demodulation 114,97
  have eq116 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq115 -- forward demodulation 115,97
  have eq156 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ X4)) := superpose eq116 eq93 -- superposition 93,116, 116 into 93, unify on (0).2 in 116 and (0).1 in 93
  have eq169 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (X0 ◇ X1)) := superpose eq93 eq113 -- superposition 113,93, 93 into 113, unify on (0).2 in 93 and (0).2 in 113
  subsumption eq169 eq156


@[equational_result]
theorem Equation3983_implies_Equation4606 (G : Type*) [Magma G] (h : Equation3983 G) : Equation4606 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq25 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq45 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = (((X0 ◇ (X1 ◇ X2)) ◇ X6) ◇ X5) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1.2 in 25
  have eq60 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).2 in 25
  have eq83 (X0 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = ((X6 ◇ X0) ◇ X5) := superpose eq9 eq45 -- forward demodulation 45,9
  have eq97 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq60 eq25 -- backward demodulation 25,60
  have eq99 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq97 eq18 -- backward demodulation 18,97
  have eq106 (X0 X3 X5 X6 : G) : ((X6 ◇ X0) ◇ X5) = (X5 ◇ (X0 ◇ X3)) := superpose eq97 eq83 -- backward demodulation 83,97
  have eq113 : ((sK0 ◇ sK0) ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq97 eq10 -- backward demodulation 10,97
  have eq114 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq99 -- forward demodulation 99,97
  have eq115 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq114 -- forward demodulation 114,97
  have eq116 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq115 -- forward demodulation 115,97
  have eq125 (X0 X5 X6 : G) : (X5 ◇ X0) = ((X6 ◇ X0) ◇ X5) := superpose eq116 eq106 -- forward demodulation 106,116
  have eq131 : (sK1 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq97 eq113 -- forward demodulation 113,97
  have eq178 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ X1) := superpose eq97 eq125 -- superposition 125,97, 97 into 125, unify on (0).2 in 97 and (0).2 in 125
  have eq258 (X0 : G) : (sK1 ◇ sK0) ≠ (sK1 ◇ X0) := superpose eq178 eq131 -- superposition 131,178, 178 into 131, unify on (0).2 in 178 and (0).2 in 131
  subsumption eq258 eq178


@[equational_result]
theorem Equation3983_implies_Equation4676 (G : Type*) [Magma G] (h : Equation3983 G) : Equation4676 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK3) ◇ sK4) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq25 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq45 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = (((X0 ◇ (X1 ◇ X2)) ◇ X6) ◇ X5) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1.2 in 25
  have eq60 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).2 in 25
  have eq83 (X0 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = ((X6 ◇ X0) ◇ X5) := superpose eq9 eq45 -- forward demodulation 45,9
  have eq97 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq60 eq25 -- backward demodulation 25,60
  have eq99 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq97 eq18 -- backward demodulation 18,97
  have eq106 (X0 X3 X5 X6 : G) : ((X6 ◇ X0) ◇ X5) = (X5 ◇ (X0 ◇ X3)) := superpose eq97 eq83 -- backward demodulation 83,97
  have eq113 : ((sK0 ◇ sK3) ◇ sK4) ≠ (sK2 ◇ sK0) := superpose eq97 eq10 -- backward demodulation 10,97
  have eq114 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq99 -- forward demodulation 99,97
  have eq115 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq114 -- forward demodulation 114,97
  have eq116 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq115 -- forward demodulation 115,97
  have eq125 (X0 X5 X6 : G) : (X5 ◇ X0) = ((X6 ◇ X0) ◇ X5) := superpose eq116 eq106 -- forward demodulation 106,116
  have eq144 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq97 eq116 -- superposition 116,97, 97 into 116, unify on (0).2 in 97 and (0).2 in 116
  have eq147 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ X2) := superpose eq97 eq144 -- forward demodulation 144,97
  have eq148 : (sK2 ◇ sK0) ≠ (sK0 ◇ sK4) := superpose eq147 eq113 -- backward demodulation 113,147
  have eq179 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ X1) := superpose eq97 eq125 -- superposition 125,97, 97 into 125, unify on (0).2 in 97 and (0).2 in 125
  have eq302 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ X1) := superpose eq125 eq147 -- superposition 147,125, 125 into 147, unify on (0).2 in 125 and (0).1 in 147
  have eq368 (X0 : G) : (sK0 ◇ sK4) ≠ (sK0 ◇ X0) := superpose eq302 eq148 -- superposition 148,302, 302 into 148, unify on (0).2 in 302 and (0).1 in 148
  subsumption eq368 eq179


@[equational_result]
theorem Equation3983_implies_Equation4519 (G : Type*) [Magma G] (h : Equation3983 G) : Equation4519 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK3) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq25 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq45 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = (((X0 ◇ (X1 ◇ X2)) ◇ X6) ◇ X5) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1.2 in 25
  have eq60 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).2 in 25
  have eq83 (X0 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = ((X6 ◇ X0) ◇ X5) := superpose eq9 eq45 -- forward demodulation 45,9
  have eq97 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq60 eq25 -- backward demodulation 25,60
  have eq99 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq97 eq18 -- backward demodulation 18,97
  have eq106 (X0 X3 X5 X6 : G) : ((X6 ◇ X0) ◇ X5) = (X5 ◇ (X0 ◇ X3)) := superpose eq97 eq83 -- backward demodulation 83,97
  have eq113 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ sK0) := superpose eq97 eq10 -- backward demodulation 10,97
  have eq114 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq99 -- forward demodulation 99,97
  have eq115 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq114 -- forward demodulation 114,97
  have eq116 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq115 -- forward demodulation 115,97
  have eq125 (X0 X5 X6 : G) : (X5 ◇ X0) = ((X6 ◇ X0) ◇ X5) := superpose eq116 eq106 -- forward demodulation 106,116
  have eq131 : (sK1 ◇ sK0) ≠ (sK0 ◇ sK1) := superpose eq116 eq113 -- forward demodulation 113,116
  have eq144 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq97 eq116 -- superposition 116,97, 97 into 116, unify on (0).2 in 97 and (0).2 in 116
  have eq147 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ X2) := superpose eq97 eq144 -- forward demodulation 144,97
  have eq178 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ X1) := superpose eq97 eq125 -- superposition 125,97, 97 into 125, unify on (0).2 in 97 and (0).2 in 125
  have eq299 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ X1) := superpose eq125 eq147 -- superposition 147,125, 125 into 147, unify on (0).2 in 125 and (0).1 in 147
  have eq347 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ X0) := superpose eq299 eq131 -- superposition 131,299, 299 into 131, unify on (0).2 in 299 and (0).1 in 131
  subsumption eq347 eq178


@[equational_result]
theorem Equation3983_implies_Equation3725 (G : Type*) [Magma G] (h : Equation3983 G) : Equation3725 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq25 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq45 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = (((X0 ◇ (X1 ◇ X2)) ◇ X6) ◇ X5) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1.2 in 25
  have eq60 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).2 in 25
  have eq83 (X0 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = ((X6 ◇ X0) ◇ X5) := superpose eq9 eq45 -- forward demodulation 45,9
  have eq97 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq60 eq25 -- backward demodulation 25,60
  have eq99 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq97 eq18 -- backward demodulation 18,97
  have eq106 (X0 X3 X5 X6 : G) : ((X6 ◇ X0) ◇ X5) = (X5 ◇ (X0 ◇ X3)) := superpose eq97 eq83 -- backward demodulation 83,97
  have eq113 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq99 -- forward demodulation 99,97
  have eq114 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq113 -- forward demodulation 113,97
  have eq115 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq114 -- forward demodulation 114,97
  have eq124 (X0 X5 X6 : G) : (X5 ◇ X0) = ((X6 ◇ X0) ◇ X5) := superpose eq115 eq106 -- forward demodulation 106,115
  have eq140 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq97 eq10 -- superposition 10,97, 97 into 10, unify on (0).2 in 97 and (0).2 in 10
  subsumption eq140 eq124


@[equational_result]
theorem Equation3983_implies_Equation3972 (G : Type*) [Magma G] (h : Equation3983 G) : Equation3972 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq19 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq26 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq46 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = (((X0 ◇ (X1 ◇ X2)) ◇ X6) ◇ X5) := superpose eq9 eq26 -- superposition 26,9, 9 into 26, unify on (0).2 in 9 and (0).1.2 in 26
  have eq61 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq26 -- superposition 26,9, 9 into 26, unify on (0).2 in 9 and (0).2 in 26
  have eq85 (X0 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = ((X6 ◇ X0) ◇ X5) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq99 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq61 eq26 -- backward demodulation 26,61
  have eq101 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq99 eq19 -- backward demodulation 19,99
  have eq108 (X0 X3 X5 X6 : G) : ((X6 ◇ X0) ◇ X5) = (X5 ◇ (X0 ◇ X3)) := superpose eq99 eq85 -- backward demodulation 85,99
  have eq115 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq99 eq101 -- forward demodulation 101,99
  have eq116 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq99 eq115 -- forward demodulation 115,99
  have eq117 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq99 eq116 -- forward demodulation 116,99
  have eq121 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK2) ◇ sK1) := superpose eq117 eq10 -- backward demodulation 10,117
  have eq127 (X0 X5 X6 : G) : (X5 ◇ X0) = ((X6 ◇ X0) ◇ X5) := superpose eq117 eq108 -- forward demodulation 108,117
  have eq187 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ X1) := superpose eq99 eq127 -- superposition 127,99, 99 into 127, unify on (0).2 in 99 and (0).2 in 127
  have eq288 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ X3) := superpose eq99 eq187 -- superposition 187,99, 99 into 187, unify on (0).2 in 99 and (0).1 in 187
  have eq317 (X0 : G) : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK2) ◇ X0) := superpose eq187 eq121 -- superposition 121,187, 187 into 121, unify on (0).2 in 187 and (0).2 in 121
  subsumption eq317 eq288


@[equational_result]
theorem Equation3983_implies_Equation4642 (G : Type*) [Magma G] (h : Equation3983 G) : Equation4642 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK2 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq25 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq45 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = (((X0 ◇ (X1 ◇ X2)) ◇ X6) ◇ X5) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1.2 in 25
  have eq60 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).2 in 25
  have eq83 (X0 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = ((X6 ◇ X0) ◇ X5) := superpose eq9 eq45 -- forward demodulation 45,9
  have eq97 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq60 eq25 -- backward demodulation 25,60
  have eq99 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq97 eq18 -- backward demodulation 18,97
  have eq106 (X0 X3 X5 X6 : G) : ((X6 ◇ X0) ◇ X5) = (X5 ◇ (X0 ◇ X3)) := superpose eq97 eq83 -- backward demodulation 83,97
  have eq113 : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ sK2) := superpose eq97 eq10 -- backward demodulation 10,97
  have eq114 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq99 -- forward demodulation 99,97
  have eq115 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq114 -- forward demodulation 114,97
  have eq116 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq115 -- forward demodulation 115,97
  have eq125 (X0 X5 X6 : G) : (X5 ◇ X0) = ((X6 ◇ X0) ◇ X5) := superpose eq116 eq106 -- forward demodulation 106,116
  have eq131 : (sK0 ◇ sK2) ≠ (sK0 ◇ sK0) := superpose eq97 eq113 -- forward demodulation 113,97
  have eq178 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ X1) := superpose eq97 eq125 -- superposition 125,97, 97 into 125, unify on (0).2 in 97 and (0).2 in 125
  have eq258 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq178 eq131 -- superposition 131,178, 178 into 131, unify on (0).2 in 178 and (0).1 in 131
  subsumption eq258 eq178


@[equational_result]
theorem Equation3983_implies_Equation3933 (G : Type*) [Magma G] (h : Equation3983 G) : Equation3933 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq19 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq26 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq46 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = (((X0 ◇ (X1 ◇ X2)) ◇ X6) ◇ X5) := superpose eq9 eq26 -- superposition 26,9, 9 into 26, unify on (0).2 in 9 and (0).1.2 in 26
  have eq61 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq26 -- superposition 26,9, 9 into 26, unify on (0).2 in 9 and (0).2 in 26
  have eq85 (X0 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = ((X6 ◇ X0) ◇ X5) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq99 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq61 eq26 -- backward demodulation 26,61
  have eq101 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq99 eq19 -- backward demodulation 19,99
  have eq108 (X0 X3 X5 X6 : G) : ((X6 ◇ X0) ◇ X5) = (X5 ◇ (X0 ◇ X3)) := superpose eq99 eq85 -- backward demodulation 85,99
  have eq115 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq99 eq101 -- forward demodulation 101,99
  have eq116 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq99 eq115 -- forward demodulation 115,99
  have eq117 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq99 eq116 -- forward demodulation 116,99
  have eq121 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK3) := superpose eq117 eq10 -- backward demodulation 10,117
  have eq127 (X0 X5 X6 : G) : (X5 ◇ X0) = ((X6 ◇ X0) ◇ X5) := superpose eq117 eq108 -- forward demodulation 108,117
  have eq147 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq99 eq117 -- superposition 117,99, 99 into 117, unify on (0).2 in 99 and (0).2 in 117
  have eq150 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ X2) := superpose eq99 eq147 -- forward demodulation 147,99
  have eq187 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ X1) := superpose eq99 eq127 -- superposition 127,99, 99 into 127, unify on (0).2 in 99 and (0).2 in 127
  have eq268 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK3) := superpose eq150 eq121 -- superposition 121,150, 150 into 121, unify on (0).2 in 150 and (0).2 in 121
  subsumption eq268 eq187


@[equational_result]
theorem Equation3983_implies_Equation313 (G : Type*) [Magma G] (h : Equation3983 G) : Equation313 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq25 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq45 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = (((X0 ◇ (X1 ◇ X2)) ◇ X6) ◇ X5) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1.2 in 25
  have eq60 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).2 in 25
  have eq83 (X0 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = ((X6 ◇ X0) ◇ X5) := superpose eq9 eq45 -- forward demodulation 45,9
  have eq97 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq60 eq25 -- backward demodulation 25,60
  have eq99 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq97 eq18 -- backward demodulation 18,97
  have eq106 (X0 X3 X5 X6 : G) : ((X6 ◇ X0) ◇ X5) = (X5 ◇ (X0 ◇ X3)) := superpose eq97 eq83 -- backward demodulation 83,97
  have eq113 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq99 -- forward demodulation 99,97
  have eq114 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq113 -- forward demodulation 113,97
  have eq115 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq114 -- forward demodulation 114,97
  have eq124 (X0 X5 X6 : G) : (X5 ◇ X0) = ((X6 ◇ X0) ◇ X5) := superpose eq115 eq106 -- forward demodulation 106,115
  have eq142 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq97 eq115 -- superposition 115,97, 97 into 115, unify on (0).2 in 97 and (0).2 in 115
  have eq145 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq115 eq10 -- superposition 10,115, 115 into 10, unify on (0).2 in 115 and (0).2 in 10
  have eq146 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ X2) := superpose eq97 eq142 -- forward demodulation 142,97
  have eq236 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ X1) := superpose eq97 eq124 -- superposition 124,97, 97 into 124, unify on (0).2 in 97 and (0).2 in 124
  have eq324 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ X1) := superpose eq124 eq146 -- superposition 146,124, 124 into 146, unify on (0).2 in 124 and (0).1 in 146
  have eq393 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq324 eq145 -- superposition 145,324, 324 into 145, unify on (0).2 in 324 and (0).2 in 145
  subsumption eq393 eq236


@[equational_result]
theorem Equation3983_implies_Equation3675 (G : Type*) [Magma G] (h : Equation3983 G) : Equation3675 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq25 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq45 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = (((X0 ◇ (X1 ◇ X2)) ◇ X6) ◇ X5) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1.2 in 25
  have eq60 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).2 in 25
  have eq83 (X0 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = ((X6 ◇ X0) ◇ X5) := superpose eq9 eq45 -- forward demodulation 45,9
  have eq97 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq60 eq25 -- backward demodulation 25,60
  have eq99 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq97 eq18 -- backward demodulation 18,97
  have eq106 (X0 X3 X5 X6 : G) : ((X6 ◇ X0) ◇ X5) = (X5 ◇ (X0 ◇ X3)) := superpose eq97 eq83 -- backward demodulation 83,97
  have eq113 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq99 -- forward demodulation 99,97
  have eq114 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq113 -- forward demodulation 113,97
  have eq115 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq114 -- forward demodulation 114,97
  have eq124 (X0 X5 X6 : G) : (X5 ◇ X0) = ((X6 ◇ X0) ◇ X5) := superpose eq115 eq106 -- forward demodulation 106,115
  have eq145 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq115 eq10 -- superposition 10,115, 115 into 10, unify on (0).2 in 115 and (0).2 in 10
  subsumption eq145 eq124


@[equational_result]
theorem Equation3983_implies_Equation3901 (G : Type*) [Magma G] (h : Equation3983 G) : Equation3901 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq19 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq26 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq30 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ (X0 ◇ X1)) = (X4 ◇ ((X2 ◇ X3) ◇ (X5 ◇ X6))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq51 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X3 ◇ (X4 ◇ X5)) ◇ X0) = ((X3 ◇ X6) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq26 -- superposition 26,9, 9 into 26, unify on (0).2 in 9 and (0).1 in 26
  have eq53 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X2 ◇ (X3 ◇ X4)) ◇ (X0 ◇ (X5 ◇ X6))) = ((X2 ◇ X7) ◇ (X0 ◇ X1)) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq61 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq26 -- superposition 26,9, 9 into 26, unify on (0).2 in 9 and (0).2 in 26
  have eq75 (X0 X1 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (X0 ◇ X1))) := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  have eq86 (X0 X1 X2 X3 X6 : G) : (X0 ◇ X3) = ((X3 ◇ X6) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq94 (X0 X1 X2 X7 : G) : ((X2 ◇ X7) ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq86 eq53 -- forward demodulation 53,86
  have eq95 (X0 X1 X2 X4 X5 : G) : (X4 ◇ (X0 ◇ X1)) = (X4 ◇ (X5 ◇ X2)) := superpose eq94 eq30 -- backward demodulation 30,94
  have eq99 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq61 eq26 -- backward demodulation 26,61
  have eq101 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq99 eq19 -- backward demodulation 19,99
  have eq115 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq99 eq101 -- forward demodulation 101,99
  have eq116 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq99 eq115 -- forward demodulation 115,99
  have eq117 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq99 eq116 -- forward demodulation 116,99
  have eq140 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq117 eq75 -- forward demodulation 75,117
  have eq161 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ X4)) := superpose eq117 eq95 -- superposition 95,117, 117 into 95, unify on (0).2 in 117 and (0).1 in 95
  have eq174 (X1 X2 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X1 ◇ X2)) := superpose eq95 eq140 -- superposition 140,95, 95 into 140, unify on (0).2 in 95 and (0).2 in 140
  subsumption eq174 eq161


@[equational_result]
theorem Equation3983_implies_Equation4506 (G : Type*) [Magma G] (h : Equation3983 G) : Equation4506 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq25 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq29 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ (X0 ◇ X1)) = (X4 ◇ ((X2 ◇ X3) ◇ (X5 ◇ X6))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq50 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X3 ◇ (X4 ◇ X5)) ◇ X0) = ((X3 ◇ X6) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1 in 25
  have eq52 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X2 ◇ (X3 ◇ X4)) ◇ (X0 ◇ (X5 ◇ X6))) = ((X2 ◇ X7) ◇ (X0 ◇ X1)) := superpose eq25 eq25 -- superposition 25,25, 25 into 25, unify on (0).2 in 25 and (0).1 in 25
  have eq60 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).2 in 25
  have eq84 (X0 X1 X2 X3 X6 : G) : (X0 ◇ X3) = ((X3 ◇ X6) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq50 -- forward demodulation 50,9
  have eq92 (X0 X1 X2 X7 : G) : ((X2 ◇ X7) ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq84 eq52 -- forward demodulation 52,84
  have eq93 (X0 X1 X2 X4 X5 : G) : (X4 ◇ (X0 ◇ X1)) = (X4 ◇ (X5 ◇ X2)) := superpose eq92 eq29 -- backward demodulation 29,92
  have eq97 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq60 eq25 -- backward demodulation 25,60
  have eq99 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq97 eq18 -- backward demodulation 18,97
  have eq113 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK0) := superpose eq97 eq10 -- backward demodulation 10,97
  have eq114 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq99 -- forward demodulation 99,97
  have eq115 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq114 -- forward demodulation 114,97
  have eq116 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq115 -- forward demodulation 115,97
  have eq156 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ X4)) := superpose eq116 eq93 -- superposition 93,116, 116 into 93, unify on (0).2 in 116 and (0).1 in 93
  have eq169 (X0 X1 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ X1)) := superpose eq93 eq113 -- superposition 113,93, 93 into 113, unify on (0).2 in 93 and (0).1 in 113
  subsumption eq169 eq156


@[equational_result]
theorem Equation3983_implies_Equation3257 (G : Type*) [Magma G] (h : Equation3983 G) : Equation3257 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq25 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq60 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).2 in 25
  have eq98 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq60 eq25 -- backward demodulation 25,60
  have eq100 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq98 eq18 -- backward demodulation 18,98
  have eq114 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq98 eq100 -- forward demodulation 100,98
  have eq115 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq98 eq114 -- forward demodulation 114,98
  have eq116 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq98 eq115 -- forward demodulation 115,98
  have eq120 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq116 eq10 -- backward demodulation 10,116
  subsumption eq120 eq116


@[equational_result]
theorem Equation3983_implies_Equation360 (G : Type*) [Magma G] (h : Equation3983 G) : Equation360 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq25 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq45 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = (((X0 ◇ (X1 ◇ X2)) ◇ X6) ◇ X5) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1.2 in 25
  have eq60 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).2 in 25
  have eq83 (X0 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = ((X6 ◇ X0) ◇ X5) := superpose eq9 eq45 -- forward demodulation 45,9
  have eq97 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq60 eq25 -- backward demodulation 25,60
  have eq99 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq97 eq18 -- backward demodulation 18,97
  have eq106 (X0 X3 X5 X6 : G) : ((X6 ◇ X0) ◇ X5) = (X5 ◇ (X0 ◇ X3)) := superpose eq97 eq83 -- backward demodulation 83,97
  have eq113 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq99 -- forward demodulation 99,97
  have eq114 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq113 -- forward demodulation 113,97
  have eq115 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq114 -- forward demodulation 114,97
  have eq124 (X0 X5 X6 : G) : (X5 ◇ X0) = ((X6 ◇ X0) ◇ X5) := superpose eq115 eq106 -- forward demodulation 106,115
  have eq177 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ X1) := superpose eq97 eq124 -- superposition 124,97, 97 into 124, unify on (0).2 in 97 and (0).2 in 124
  have eq243 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ X3) := superpose eq97 eq177 -- superposition 177,97, 97 into 177, unify on (0).2 in 97 and (0).1 in 177
  have eq270 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ X0) := superpose eq177 eq10 -- superposition 10,177, 177 into 10, unify on (0).2 in 177 and (0).2 in 10
  subsumption eq270 eq243


@[equational_result]
theorem Equation3983_implies_Equation3759 (G : Type*) [Magma G] (h : Equation3983 G) : Equation3759 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq25 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq45 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = (((X0 ◇ (X1 ◇ X2)) ◇ X6) ◇ X5) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1.2 in 25
  have eq60 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).2 in 25
  have eq83 (X0 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = ((X6 ◇ X0) ◇ X5) := superpose eq9 eq45 -- forward demodulation 45,9
  have eq97 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq60 eq25 -- backward demodulation 25,60
  have eq99 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq97 eq18 -- backward demodulation 18,97
  have eq106 (X0 X3 X5 X6 : G) : ((X6 ◇ X0) ◇ X5) = (X5 ◇ (X0 ◇ X3)) := superpose eq97 eq83 -- backward demodulation 83,97
  have eq113 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq99 -- forward demodulation 99,97
  have eq114 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq113 -- forward demodulation 113,97
  have eq115 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq114 -- forward demodulation 114,97
  have eq124 (X0 X5 X6 : G) : (X5 ◇ X0) = ((X6 ◇ X0) ◇ X5) := superpose eq115 eq106 -- forward demodulation 106,115
  have eq144 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq115 eq10 -- superposition 10,115, 115 into 10, unify on (0).2 in 115 and (0).2 in 10
  subsumption eq144 eq124


@[equational_result]
theorem Equation3983_implies_Equation3681 (G : Type*) [Magma G] (h : Equation3983 G) : Equation3681 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq25 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq27 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : (X7 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X8 ◇ X9))) = ((((X5 ◇ X6) ◇ X2) ◇ (X0 ◇ X1)) ◇ X7) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq38 (X0 X1 X2 X5 X6 X7 X8 X9 : G) : ((((X5 ◇ X6) ◇ X2) ◇ (X0 ◇ X1)) ◇ X7) = (X7 ◇ ((X8 ◇ X9) ◇ X2)) := superpose eq9 eq27 -- forward demodulation 27,9
  have eq45 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = (((X0 ◇ (X1 ◇ X2)) ◇ X6) ◇ X5) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1.2 in 25
  have eq50 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X3 ◇ (X4 ◇ X5)) ◇ X0) = ((X3 ◇ X6) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1 in 25
  have eq52 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X2 ◇ (X3 ◇ X4)) ◇ (X0 ◇ (X5 ◇ X6))) = ((X2 ◇ X7) ◇ (X0 ◇ X1)) := superpose eq25 eq25 -- superposition 25,25, 25 into 25, unify on (0).2 in 25 and (0).1 in 25
  have eq60 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).2 in 25
  have eq83 (X0 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = ((X6 ◇ X0) ◇ X5) := superpose eq9 eq45 -- forward demodulation 45,9
  have eq84 (X0 X1 X2 X3 X6 : G) : (X0 ◇ X3) = ((X3 ◇ X6) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq50 -- forward demodulation 50,9
  have eq92 (X0 X1 X2 X7 : G) : ((X2 ◇ X7) ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq84 eq52 -- forward demodulation 52,84
  have eq94 (X0 X2 X5 X6 X7 X8 X9 : G) : (X7 ◇ ((X8 ◇ X9) ◇ X2)) = ((X0 ◇ (X5 ◇ X6)) ◇ X7) := superpose eq92 eq38 -- backward demodulation 38,92
  have eq97 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq60 eq25 -- backward demodulation 25,60
  have eq99 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq97 eq18 -- backward demodulation 18,97
  have eq106 (X0 X3 X5 X6 : G) : ((X6 ◇ X0) ◇ X5) = (X5 ◇ (X0 ◇ X3)) := superpose eq97 eq83 -- backward demodulation 83,97
  have eq112 (X0 X2 X5 X6 X7 X8 : G) : ((X0 ◇ (X5 ◇ X6)) ◇ X7) = (X7 ◇ (X2 ◇ X8)) := superpose eq97 eq94 -- backward demodulation 94,97
  have eq113 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq99 -- forward demodulation 99,97
  have eq114 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq113 -- forward demodulation 113,97
  have eq115 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq114 -- forward demodulation 114,97
  have eq124 (X0 X5 X6 : G) : (X5 ◇ X0) = ((X6 ◇ X0) ◇ X5) := superpose eq115 eq106 -- forward demodulation 106,115
  have eq129 (X0 X2 X5 X7 X8 : G) : (X7 ◇ (X2 ◇ X8)) = ((X0 ◇ X5) ◇ X7) := superpose eq115 eq112 -- forward demodulation 112,115
  have eq187 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = ((X3 ◇ X4) ◇ X0) := superpose eq115 eq129 -- superposition 129,115, 115 into 129, unify on (0).2 in 115 and (0).1 in 129
  have eq235 : (sK0 ◇ sK0) ≠ ((sK2 ◇ sK1) ◇ sK0) := superpose eq124 eq10 -- superposition 10,124, 124 into 10, unify on (0).2 in 124 and (0).2 in 10
  subsumption eq235 eq187


@[equational_result]
theorem Equation3983_implies_Equation3515 (G : Type*) [Magma G] (h : Equation3983 G) : Equation3515 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq25 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq60 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).2 in 25
  have eq97 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq60 eq25 -- backward demodulation 25,60
  have eq99 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq97 eq18 -- backward demodulation 18,97
  have eq113 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq97 eq10 -- backward demodulation 10,97
  have eq114 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq99 -- forward demodulation 99,97
  have eq115 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq114 -- forward demodulation 114,97
  have eq116 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq115 -- forward demodulation 115,97
  subsumption eq113 eq116


@[equational_result]
theorem Equation3983_implies_Equation3525 (G : Type*) [Magma G] (h : Equation3983 G) : Equation3525 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq25 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq60 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).2 in 25
  have eq97 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq60 eq25 -- backward demodulation 25,60
  have eq99 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq97 eq18 -- backward demodulation 18,97
  have eq113 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq97 eq10 -- backward demodulation 10,97
  have eq114 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq99 -- forward demodulation 99,97
  have eq115 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq114 -- forward demodulation 114,97
  have eq116 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq97 eq115 -- forward demodulation 115,97
  subsumption eq113 eq116


@[equational_result]
theorem Equation3983_implies_Equation3892 (G : Type*) [Magma G] (h : Equation3983 G) : Equation3892 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = (((X3 ◇ X4) ◇ X0) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq19 (X0 X1 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq26 (X0 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X6))) = ((X3 ◇ X0) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq46 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = (((X0 ◇ (X1 ◇ X2)) ◇ X6) ◇ X5) := superpose eq9 eq26 -- superposition 26,9, 9 into 26, unify on (0).2 in 9 and (0).1.2 in 26
  have eq61 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq9 eq26 -- superposition 26,9, 9 into 26, unify on (0).2 in 9 and (0).2 in 26
  have eq85 (X0 X3 X4 X5 X6 : G) : (X5 ◇ ((X3 ◇ X4) ◇ X0)) = ((X6 ◇ X0) ◇ X5) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq99 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X4 ◇ X3) := superpose eq61 eq26 -- backward demodulation 26,61
  have eq101 (X0 X1 X4 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ ((X1 ◇ X4) ◇ X0)) := superpose eq99 eq19 -- backward demodulation 19,99
  have eq108 (X0 X3 X5 X6 : G) : ((X6 ◇ X0) ◇ X5) = (X5 ◇ (X0 ◇ X3)) := superpose eq99 eq85 -- backward demodulation 85,99
  have eq115 (X0 X1 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X0) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq99 eq101 -- forward demodulation 101,99
  have eq116 (X0 X1 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = (X6 ◇ (X0 ◇ X1)) := superpose eq99 eq115 -- forward demodulation 115,99
  have eq117 (X0 X1 X6 : G) : (X6 ◇ X0) = (X6 ◇ (X0 ◇ X1)) := superpose eq99 eq116 -- forward demodulation 116,99
  have eq121 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ sK2) := superpose eq117 eq10 -- backward demodulation 10,117
  have eq127 (X0 X5 X6 : G) : (X5 ◇ X0) = ((X6 ◇ X0) ◇ X5) := superpose eq117 eq108 -- forward demodulation 108,117
  have eq147 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq99 eq117 -- superposition 117,99, 99 into 117, unify on (0).2 in 99 and (0).2 in 117
  have eq150 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ X2) := superpose eq99 eq147 -- forward demodulation 147,99
  have eq320 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ X1) := superpose eq127 eq150 -- superposition 150,127, 127 into 150, unify on (0).2 in 127 and (0).1 in 150
  have eq432 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq320 eq320 -- superposition 320,320, 320 into 320, unify on (0).2 in 320 and (0).1 in 320
  have eq493 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq320 eq121 -- superposition 121,320, 320 into 121, unify on (0).2 in 320 and (0).2 in 121
  subsumption eq493 eq432


@[equational_result]
theorem Equation3287_implies_Equation3288 (G : Type*) [Magma G] (h : Equation3287 G) : Equation3288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X3 X4 : G) : (X4 ◇ X4) = (X0 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq58 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2 in 10
  subsumption eq58 eq14


@[equational_result]
theorem Equation3287_implies_Equation3678 (G : Type*) [Magma G] (h : Equation3287 G) : Equation3678 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq14 (X0 X3 X4 : G) : (X4 ◇ X4) = (X0 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq23 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2 in 10
  subsumption eq23 eq14


@[equational_result]
theorem Equation3287_implies_Equation4355 (G : Type*) [Magma G] (h : Equation3287 G) : Equation4355 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq14 (X0 X3 X4 : G) : (X4 ◇ X4) = (X0 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq52 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq52 eq14


@[equational_result]
theorem Equation3287_implies_Equation3272 (G : Type*) [Magma G] (h : Equation3287 G) : Equation3272 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq14 (X0 X3 X4 : G) : (X4 ◇ X4) = (X0 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq52 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2 in 10
  subsumption eq52 eq14


@[equational_result]
theorem Equation3287_implies_Equation3674 (G : Type*) [Magma G] (h : Equation3287 G) : Equation3674 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq14 (X0 X3 X4 : G) : (X4 ◇ X4) = (X0 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq26 (X0 : G) : (X0 ◇ X0) ≠ ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).1 in 10
  subsumption eq26 eq14


@[equational_result]
theorem Equation3287_implies_Equation3694 (G : Type*) [Magma G] (h : Equation3287 G) : Equation3694 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq14 (X0 X3 X4 : G) : (X4 ◇ X4) = (X0 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq26 (X0 : G) : (X0 ◇ X0) ≠ ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).1 in 10
  subsumption eq26 eq14


@[equational_result]
theorem Equation3287_implies_Equation3266 (G : Type*) [Magma G] (h : Equation3287 G) : Equation3266 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq14 (X0 X3 X4 : G) : (X4 ◇ X4) = (X0 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq58 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2 in 10
  subsumption eq58 eq14


@[equational_result]
theorem Equation3287_implies_Equation312 (G : Type*) [Magma G] (h : Equation3287 G) : Equation312 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq14 (X0 X3 X4 : G) : (X4 ◇ X4) = (X0 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq23 (X0 : G) : (X0 ◇ X0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).1 in 10
  subsumption eq23 eq14


@[equational_result]
theorem Equation3287_implies_Equation3303 (G : Type*) [Magma G] (h : Equation3287 G) : Equation3303 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3))) := mod_symm nh
  have eq14 (X0 X3 X4 : G) : (X4 ◇ X4) = (X0 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq58 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2 in 10
  subsumption eq58 eq14


@[equational_result]
theorem Equation3695_implies_Equation3662 (G : Type*) [Magma G] (h : Equation3695 G) : Equation3662 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq91 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq9 eq24 -- superposition 24,9, 9 into 24, unify on (0).2 in 9 and (0).2.1 in 24
  have eq249 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq91 -- superposition 91,9, 9 into 91, unify on (0).2 in 9 and (0).2 in 91
  have eq281 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq91 eq10 -- superposition 10,91, 91 into 10, unify on (0).2 in 91 and (0).2 in 10
  subsumption eq281 eq249


@[equational_result]
theorem Equation3695_implies_Equation3668 (G : Type*) [Magma G] (h : Equation3695 G) : Equation3668 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq91 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq9 eq24 -- superposition 24,9, 9 into 24, unify on (0).2 in 9 and (0).2.1 in 24
  have eq249 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq91 -- superposition 91,9, 9 into 91, unify on (0).2 in 9 and (0).2 in 91
  have eq265 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X2)) = ((X0 ◇ X3) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) := superpose eq91 eq9 -- superposition 9,91, 91 into 9, unify on (0).2 in 91 and (0).2.2 in 9
  have eq347 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq91 eq13 -- superposition 13,91, 91 into 13, unify on (0).2 in 91 and (0).2.1 in 13
  have eq428 (X0 X2 X3 : G) : (X2 ◇ X2) = ((X0 ◇ X3) ◇ (X2 ◇ X2)) := superpose eq347 eq265 -- backward demodulation 265,347
  have eq1879 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq428 eq10 -- superposition 10,428, 428 into 10, unify on (0).2 in 428 and (0).2 in 10
  subsumption eq1879 eq249


@[equational_result]
theorem Equation3695_implies_Equation3661 (G : Type*) [Magma G] (h : Equation3695 G) : Equation3661 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X3 ◇ X4) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X2 ◇ X0) ◇ X3) ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq124 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (sK1 ◇ X0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq374 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq13 eq16 -- superposition 16,13, 13 into 16, unify on (0).2 in 13 and (0).2 in 16
  have eq839 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq374 eq124 -- superposition 124,374, 374 into 124, unify on (0).2 in 374 and (0).2 in 124
  subsumption eq839 eq374


@[equational_result]
theorem Equation3695_implies_Equation4341 (G : Type*) [Magma G] (h : Equation3695 G) : Equation4341 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq91 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq9 eq24 -- superposition 24,9, 9 into 24, unify on (0).2 in 9 and (0).2.1 in 24
  have eq249 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq91 -- superposition 91,9, 9 into 91, unify on (0).2 in 9 and (0).2 in 91
  have eq532 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq249 eq10 -- superposition 10,249, 249 into 10, unify on (0).2 in 249 and (0).2.2 in 10
  subsumption eq532 rfl


@[equational_result]
theorem Equation3695_implies_Equation3703 (G : Type*) [Magma G] (h : Equation3695 G) : Equation3703 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X3 ◇ X4) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X2 ◇ X0) ◇ X3) ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq121 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (sK2 ◇ X0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq374 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq13 eq16 -- superposition 16,13, 13 into 16, unify on (0).2 in 13 and (0).2 in 16
  have eq832 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq374 eq121 -- superposition 121,374, 374 into 121, unify on (0).2 in 374 and (0).2 in 121
  subsumption eq832 eq374


@[equational_result]
theorem Equation3695_implies_Equation40 (G : Type*) [Magma G] (h : Equation3695 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq91 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq9 eq24 -- superposition 24,9, 9 into 24, unify on (0).2 in 9 and (0).2.1 in 24
  have eq249 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq91 -- superposition 91,9, 9 into 91, unify on (0).2 in 9 and (0).2 in 91
  have eq500 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq249 eq10 -- superposition 10,249, 249 into 10, unify on (0).2 in 249 and (0).2 in 10
  subsumption eq500 eq249


@[equational_result]
theorem Equation3695_implies_Equation3709 (G : Type*) [Magma G] (h : Equation3695 G) : Equation3709 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq91 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq9 eq24 -- superposition 24,9, 9 into 24, unify on (0).2 in 9 and (0).2.1 in 24
  have eq249 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq91 -- superposition 91,9, 9 into 91, unify on (0).2 in 9 and (0).2 in 91
  have eq265 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X2)) = ((X0 ◇ X3) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) := superpose eq91 eq9 -- superposition 9,91, 91 into 9, unify on (0).2 in 91 and (0).2.2 in 9
  have eq347 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq91 eq13 -- superposition 13,91, 91 into 13, unify on (0).2 in 91 and (0).2.1 in 13
  have eq428 (X0 X2 X3 : G) : (X2 ◇ X2) = ((X0 ◇ X3) ◇ (X2 ◇ X2)) := superpose eq347 eq265 -- backward demodulation 265,347
  have eq1865 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq428 eq10 -- superposition 10,428, 428 into 10, unify on (0).2 in 428 and (0).2 in 10
  subsumption eq1865 eq249


@[equational_result]
theorem Equation3695_implies_Equation3693 (G : Type*) [Magma G] (h : Equation3695 G) : Equation3693 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq91 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq9 eq24 -- superposition 24,9, 9 into 24, unify on (0).2 in 9 and (0).2.1 in 24
  have eq249 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq91 -- superposition 91,9, 9 into 91, unify on (0).2 in 9 and (0).2 in 91
  have eq347 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq91 eq13 -- superposition 13,91, 91 into 13, unify on (0).2 in 91 and (0).2.1 in 13
  have eq1531 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq347 eq10 -- superposition 10,347, 347 into 10, unify on (0).2 in 347 and (0).2 in 10
  subsumption eq1531 eq249


@[equational_result]
theorem Equation3695_implies_Equation3684 (G : Type*) [Magma G] (h : Equation3695 G) : Equation3684 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq91 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq9 eq24 -- superposition 24,9, 9 into 24, unify on (0).2 in 9 and (0).2.1 in 24
  have eq249 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq91 -- superposition 91,9, 9 into 91, unify on (0).2 in 9 and (0).2 in 91
  have eq281 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq91 eq10 -- superposition 10,91, 91 into 10, unify on (0).2 in 91 and (0).2 in 10
  subsumption eq281 eq249


@[equational_result]
theorem Equation3695_implies_Equation3665 (G : Type*) [Magma G] (h : Equation3695 G) : Equation3665 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq91 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq9 eq24 -- superposition 24,9, 9 into 24, unify on (0).2 in 9 and (0).2.1 in 24
  have eq258 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq91 eq10 -- superposition 10,91, 91 into 10, unify on (0).2 in 91 and (0).2 in 10
  subsumption eq258 eq91


@[equational_result]
theorem Equation3695_implies_Equation3670 (G : Type*) [Magma G] (h : Equation3695 G) : Equation3670 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X3 ◇ X4) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X2 ◇ X0) ◇ X3) ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq121 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (sK2 ◇ X0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq374 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq13 eq16 -- superposition 16,13, 13 into 16, unify on (0).2 in 13 and (0).2 in 16
  have eq832 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq374 eq121 -- superposition 121,374, 374 into 121, unify on (0).2 in 374 and (0).2 in 121
  subsumption eq832 eq374


@[equational_result]
theorem Equation3695_implies_Equation3707 (G : Type*) [Magma G] (h : Equation3695 G) : Equation3707 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X3 ◇ X4) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X2 ◇ X0) ◇ X3) ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq121 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (sK3 ◇ X0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq374 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq13 eq16 -- superposition 16,13, 13 into 16, unify on (0).2 in 13 and (0).2 in 16
  have eq832 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq374 eq121 -- superposition 121,374, 374 into 121, unify on (0).2 in 374 and (0).2 in 121
  subsumption eq832 eq374


@[equational_result]
theorem Equation2156_implies_Equation588 (G : Type*) [Magma G] (h : Equation2156 G) : Equation588 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation2156_implies_Equation4121 (G : Type*) [Magma G] (h : Equation2156 G) : Equation4121 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X2 X3 X4 : G) : (X2 ◇ X3) = (X4 ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq39 (X0 : G) : (sK0 ◇ sK1) ≠ (((X0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.1.1 in 10
  subsumption eq39 eq14


@[equational_result]
theorem Equation2156_implies_Equation1374 (G : Type*) [Magma G] (h : Equation2156 G) : Equation1374 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK1) ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2156_implies_Equation1657 (G : Type*) [Magma G] (h : Equation2156 G) : Equation1657 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation2156_implies_Equation1028 (G : Type*) [Magma G] (h : Equation2156 G) : Equation1028 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation2156_implies_Equation2100 (G : Type*) [Magma G] (h : Equation2156 G) : Equation2100 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation2156_implies_Equation1672 (G : Type*) [Magma G] (h : Equation2156 G) : Equation1672 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2156_implies_Equation3264 (G : Type*) [Magma G] (h : Equation2156 G) : Equation3264 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 rfl


@[equational_result]
theorem Equation3070_implies_Equation3098 (G : Type*) [Magma G] (h : Equation3070 G) : Equation3098 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK3) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK3) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq31 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) ◇ X3) = (((((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) ◇ X3)) ◇ X4) ◇ X5) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq54 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) ◇ X3) = (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X4) ◇ X5) := superpose eq11 eq31 -- forward demodulation 31,11
  have eq55 (X0 X1 X2 X3 X5 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) ◇ X3) = (X0 ◇ X5) := superpose eq9 eq54 -- forward demodulation 54,9
  have eq56 (X0 X3 X5 : G) : (X0 ◇ X3) = (X0 ◇ X5) := superpose eq9 eq55 -- forward demodulation 55,9
  have eq80 (X0 X1 X2 X3 : G) : ((((X0 ◇ X2) ◇ X0) ◇ X1) ◇ X3) = X0 := superpose eq56 eq9 -- superposition 9,56, 56 into 9, unify on (0).2 in 56 and (0).1.1.1.1 in 9
  have eq93 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK3) ◇ X0) := superpose eq56 eq13 -- superposition 13,56, 56 into 13, unify on (0).2 in 56 and (0).2 in 13
  subsumption eq93 eq80


@[equational_result]
theorem Equation3070_implies_Equation3101 (G : Type*) [Magma G] (h : Equation3070 G) : Equation3101 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK3) ◇ sK4) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK3) ◇ sK4) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq31 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) ◇ X3) = (((((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) ◇ X3)) ◇ X4) ◇ X5) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq54 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) ◇ X3) = (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X4) ◇ X5) := superpose eq11 eq31 -- forward demodulation 31,11
  have eq55 (X0 X1 X2 X3 X5 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) ◇ X3) = (X0 ◇ X5) := superpose eq9 eq54 -- forward demodulation 54,9
  have eq56 (X0 X3 X5 : G) : (X0 ◇ X3) = (X0 ◇ X5) := superpose eq9 eq55 -- forward demodulation 55,9
  have eq80 (X0 X1 X2 X3 : G) : ((((X0 ◇ X2) ◇ X0) ◇ X1) ◇ X3) = X0 := superpose eq56 eq9 -- superposition 9,56, 56 into 9, unify on (0).2 in 56 and (0).1.1.1.1 in 9
  have eq93 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ X0) ◇ sK4) := superpose eq56 eq13 -- superposition 13,56, 56 into 13, unify on (0).2 in 56 and (0).2.1 in 13
  subsumption eq93 eq80


@[equational_result]
theorem Equation3070_implies_Equation3324 (G : Type*) [Magma G] (h : Equation3070 G) : Equation3324 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq27 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) ◇ X3) = (((((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) ◇ X3)) ◇ X4) ◇ X5) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq49 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) ◇ X3) = (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X4) ◇ X5) := superpose eq11 eq27 -- forward demodulation 27,11
  have eq50 (X0 X1 X2 X3 X5 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) ◇ X3) = (X0 ◇ X5) := superpose eq9 eq49 -- forward demodulation 49,9
  have eq51 (X0 X3 X5 : G) : (X0 ◇ X3) = (X0 ◇ X5) := superpose eq9 eq50 -- forward demodulation 50,9
  have eq86 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ X0) := superpose eq51 eq10 -- superposition 10,51, 51 into 10, unify on (0).2 in 51 and (0).2 in 10
  subsumption eq86 eq51


@[equational_result]
theorem Equation3070_implies_Equation3317 (G : Type*) [Magma G] (h : Equation3070 G) : Equation3317 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq27 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) ◇ X3) = (((((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) ◇ X3)) ◇ X4) ◇ X5) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq49 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) ◇ X3) = (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X4) ◇ X5) := superpose eq11 eq27 -- forward demodulation 27,11
  have eq50 (X0 X1 X2 X3 X5 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) ◇ X3) = (X0 ◇ X5) := superpose eq9 eq49 -- forward demodulation 49,9
  have eq51 (X0 X3 X5 : G) : (X0 ◇ X3) = (X0 ◇ X5) := superpose eq9 eq50 -- forward demodulation 50,9
  have eq86 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ X0))) := superpose eq51 eq10 -- superposition 10,51, 51 into 10, unify on (0).2 in 51 and (0).2.2.2 in 10
  subsumption eq86 eq51


@[equational_result]
theorem Equation2869_implies_Equation2851 (G : Type*) [Magma G] (h : Equation2869 G) : Equation2851 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = (X1 ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq22 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X1) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq71 (X0 : G) : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ sK2) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq71 eq22


@[equational_result]
theorem Equation2869_implies_Equation3309 (G : Type*) [Magma G] (h : Equation2869 G) : Equation3309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = (X1 ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq26 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (X0 ◇ sK0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq26 eq13


@[equational_result]
theorem Equation637_implies_Equation4382 (G : Type*) [Magma G] (h : Equation637 G) : Equation4382 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X0 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq17 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq14 -- backward demodulation 14,12
  subsumption eq17 eq12


@[equational_result]
theorem Equation637_implies_Equation3736 (G : Type*) [Magma G] (h : Equation637 G) : Equation3736 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq16 -- forward demodulation 16,12
  subsumption eq17 rfl


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
theorem Equation637_implies_Equation3876 (G : Type*) [Magma G] (h : Equation637 G) : Equation3876 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK3) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq16 -- forward demodulation 16,12
  subsumption eq17 eq12


@[equational_result]
theorem Equation637_implies_Equation4514 (G : Type*) [Magma G] (h : Equation637 G) : Equation4514 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq16 -- forward demodulation 16,12
  subsumption eq17 eq12


@[equational_result]
theorem Equation637_implies_Equation3932 (G : Type*) [Magma G] (h : Equation637 G) : Equation3932 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq16 -- forward demodulation 16,12
  subsumption eq17 eq12


@[equational_result]
theorem Equation3370_implies_Equation4677 (G : Type*) [Magma G] (h : Equation3370 G) : Equation4677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK1 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X3) = (X3 ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 : ((sK0 ◇ sK1) ◇ sK2) ≠ (sK2 ◇ (sK0 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq19 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq52 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ (X2 ◇ X1)) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq97 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq52 eq19 -- backward demodulation 19,52
  have eq253 : (sK2 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK0 ◇ sK1)) := superpose eq97 eq13 -- superposition 13,97, 97 into 13, unify on (0).2 in 97 and (0).1 in 13
  subsumption eq253 rfl


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
theorem Equation3080_implies_Equation4358 (G : Type*) [Magma G] (h : Equation3080 G) : Equation4358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation3080_implies_Equation3264 (G : Type*) [Magma G] (h : Equation3080 G) : Equation3264 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation3080_implies_Equation3469 (G : Type*) [Magma G] (h : Equation3080 G) : Equation3469 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation3080_implies_Equation3052 (G : Type*) [Magma G] (h : Equation3080 G) : Equation3052 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq9


@[equational_result]
theorem Equation3080_implies_Equation3263 (G : Type*) [Magma G] (h : Equation3080 G) : Equation3263 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation651_implies_Equation1067 (G : Type*) [Magma G] (h : Equation651 G) : Equation1067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation651_implies_Equation3932 (G : Type*) [Magma G] (h : Equation651 G) : Equation3932 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation651_implies_Equation459 (G : Type*) [Magma G] (h : Equation651 G) : Equation459 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1)))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation651_implies_Equation4383 (G : Type*) [Magma G] (h : Equation651 G) : Equation4383 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation651_implies_Equation1231 (G : Type*) [Magma G] (h : Equation651 G) : Equation1231 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation651_implies_Equation54 (G : Type*) [Magma G] (h : Equation651 G) : Equation54 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation651_implies_Equation1255 (G : Type*) [Magma G] (h : Equation651 G) : Equation1255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation651_implies_Equation4517 (G : Type*) [Magma G] (h : Equation651 G) : Equation4517 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK2) ◇ sK3) := mod_symm nh
  have eq12 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK3) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK3) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation651_implies_Equation1236 (G : Type*) [Magma G] (h : Equation651 G) : Equation1236 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK2) ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation651_implies_Equation1227 (G : Type*) [Magma G] (h : Equation651 G) : Equation1227 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation1836_implies_Equation1433 (G : Type*) [Magma G] (h : Equation1836 G) : Equation1433 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq13 (X0 X3 : G) : ((X3 ◇ (X3 ◇ X3)) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ X1) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq50 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ X1) := superpose eq22 eq22 -- superposition 22,22, 22 into 22, unify on (0).2 in 22 and (0).1 in 22
  have eq55 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq22 eq13 -- superposition 13,22, 22 into 13, unify on (0).2 in 22 and (0).1.1 in 13
  have eq129 (X0 : G) : sK0 ≠ ((sK0 ◇ sK0) ◇ X0) := superpose eq50 eq10 -- superposition 10,50, 50 into 10, unify on (0).2 in 50 and (0).2 in 10
  subsumption eq129 eq55


@[equational_result]
theorem Equation875_implies_Equation4243 (G : Type*) [Magma G] (h : Equation875 G) : Equation4243 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK3) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 (X0 : G) : (sK0 ◇ sK1) ≠ (((X0 ◇ sK3) ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq22 eq13


@[equational_result]
theorem Equation875_implies_Equation1618 (G : Type*) [Magma G] (h : Equation875 G) : Equation1618 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq28 (X0 : G) : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ (X0 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.2 in 10
  subsumption eq28 eq26


@[equational_result]
theorem Equation434_implies_Equation1234 (G : Type*) [Magma G] (h : Equation434 G) : Equation1234 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation434_implies_Equation846 (G : Type*) [Magma G] (h : Equation434 G) : Equation846 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation434_implies_Equation3663 (G : Type*) [Magma G] (h : Equation434 G) : Equation3663 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq23 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq23 rfl


@[equational_result]
theorem Equation434_implies_Equation845 (G : Type*) [Magma G] (h : Equation434 G) : Equation845 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq17 eq12


