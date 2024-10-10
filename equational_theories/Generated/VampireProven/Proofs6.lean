import equational_theories.Superposition
import equational_theories.Equations.All
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation2567_implies_Equation2706 (G : Type*) [Magma G] (h : Equation2567 G) : Equation2706 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq25 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq20 eq10 -- backward demodulation 10,20
  have eq27 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq33 : sK0 ≠ sK0 := superpose eq27 eq25 -- superposition 25,27, 27 into 25, unify on (0).2 in 27 and (0).2 in 25
  subsumption eq33 rfl


@[equational_result]
theorem Equation2567_implies_Equation2770 (G : Type*) [Magma G] (h : Equation2567 G) : Equation2770 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2567_implies_Equation2919 (G : Type*) [Magma G] (h : Equation2567 G) : Equation2919 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq32 : sK0 ≠ sK0 := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq32 rfl


@[equational_result]
theorem Equation2567_implies_Equation2973 (G : Type*) [Magma G] (h : Equation2567 G) : Equation2973 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq32 : sK0 ≠ sK0 := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq32 rfl


@[equational_result]
theorem Equation2567_implies_Equation2990 (G : Type*) [Magma G] (h : Equation2567 G) : Equation2990 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK1)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq32 : sK0 ≠ sK0 := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq32 rfl


@[equational_result]
theorem Equation2567_implies_Equation3024 (G : Type*) [Magma G] (h : Equation2567 G) : Equation3024 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq32 : sK0 ≠ sK0 := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq32 rfl


@[equational_result]
theorem Equation2567_implies_Equation3122 (G : Type*) [Magma G] (h : Equation2567 G) : Equation3122 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK2) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq32 : sK0 ≠ sK0 := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq32 rfl


@[equational_result]
theorem Equation2567_implies_Equation3210 (G : Type*) [Magma G] (h : Equation2567 G) : Equation3210 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK2) ◇ sK2) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq29 : sK0 ≠ ((sK2 ◇ sK0) ◇ sK0) := superpose eq26 eq10 -- backward demodulation 10,26
  subsumption eq29 eq26


@[equational_result]
theorem Equation2567_implies_Equation3533 (G : Type*) [Magma G] (h : Equation2567 G) : Equation3533 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq29 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq26 eq10 -- backward demodulation 10,26
  subsumption eq29 rfl


@[equational_result]
theorem Equation2567_implies_Equation364 (G : Type*) [Magma G] (h : Equation2567 G) : Equation364 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq27 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq27 eq26


@[equational_result]
theorem Equation2567_implies_Equation4192 (G : Type*) [Magma G] (h : Equation2567 G) : Equation4192 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq29 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq26 eq10 -- backward demodulation 10,26
  subsumption eq29 rfl


@[equational_result]
theorem Equation2567_implies_Equation4385 (G : Type*) [Magma G] (h : Equation2567 G) : Equation4385 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq27 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq20 eq10 -- backward demodulation 10,20
  have eq30 : sK0 ≠ (sK0 ◇ sK0) := superpose eq26 eq27 -- forward demodulation 27,26
  subsumption eq30 eq20


@[equational_result]
theorem Equation2567_implies_Equation832 (G : Type*) [Magma G] (h : Equation2567 G) : Equation832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq27 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := superpose eq20 eq10 -- backward demodulation 10,20
  have eq30 : sK0 ≠ (sK0 ◇ sK0) := superpose eq26 eq27 -- forward demodulation 27,26
  subsumption eq30 eq20


@[equational_result]
theorem Equation2571_implies_Equation221 (G : Type*) [Magma G] (h : Equation2571 G) : Equation221 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2571_implies_Equation2724 (G : Type*) [Magma G] (h : Equation2571 G) : Equation2724 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK2 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq125 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.1 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.1.1 in 20
  have eq185 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq148 -- superposition 148,15, 15 into 148, unify on (0).2 in 15 and (0).2.1 in 148
  have eq520 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2) = X2 := superpose eq185 eq9 -- superposition 9,185, 185 into 9, unify on (0).2 in 185 and (0).1.1 in 9
  have eq899 : sK0 ≠ sK0 := superpose eq520 eq10 -- superposition 10,520, 520 into 10, unify on (0).2 in 520 and (0).2 in 10
  subsumption eq899 rfl


@[equational_result]
theorem Equation257_implies_Equation2849 (G : Type*) [Magma G] (h : Equation257 G) : Equation2849 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq12 eq9


@[equational_result]
theorem Equation257_implies_Equation307 (G : Type*) [Magma G] (h : Equation257 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq11 rfl


@[equational_result]
theorem Equation2573_implies_Equation1155 (G : Type*) [Magma G] (h : Equation2573 G) : Equation1155 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ ((X3 ◇ X1) ◇ X2)) ◇ X3) ◇ (X4 ◇ ((X5 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X4))) = X5 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq22 (X0 X1 X4 X5 : G) : (X1 ◇ (X4 ◇ ((X5 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X4))) = X5 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq29 (X0 X1 X3 X4 : G) : (X0 ◇ (X1 ◇ X0)) = ((X3 ◇ X1) ◇ (X4 ◇ (X3 ◇ X4))) := superpose eq11 eq22 -- superposition 22,11, 11 into 22, unify on (0).2 in 11 and (0).1.2.2.1 in 22
  have eq54 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X4)) = ((X3 ◇ (X1 ◇ X3)) ◇ (X5 ◇ ((X0 ◇ X1) ◇ X5))) := superpose eq29 eq29 -- superposition 29,29, 29 into 29, unify on (0).2 in 29 and (0).2.1 in 29
  have eq99 (X0 X2 X4 : G) : (X4 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X4)) = X0 := superpose eq11 eq54 -- forward demodulation 54,11
  have eq202 : sK0 ≠ sK0 := superpose eq99 eq10 -- superposition 10,99, 99 into 10, unify on (0).2 in 99 and (0).2 in 10
  subsumption eq202 rfl


@[equational_result]
theorem Equation2575_implies_Equation2525 (G : Type*) [Magma G] (h : Equation2575 G) : Equation2525 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK2) ◇ sK3)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1)))) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq13 (X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X2) = X2 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq52 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq14 eq13 -- superposition 13,14, 14 into 13, unify on (0).2 in 14 and (0).1.1 in 13
  have eq62 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X2) = X2 := superpose eq52 eq11 -- backward demodulation 11,52
  have eq75 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = ((X2 ◇ (X3 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq9 eq62 -- superposition 62,9, 9 into 62, unify on (0).2 in 9 and (0).1.1.2.2 in 62
  have eq258 (X0 X1 X2 : G) : (X2 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) := superpose eq75 eq13 -- superposition 13,75, 75 into 13, unify on (0).2 in 75 and (0).1.1 in 13
  have eq394 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq258 eq13 -- superposition 13,258, 258 into 13, unify on (0).2 in 258 and (0).1.1 in 13
  have eq438 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq394 eq9 -- backward demodulation 9,394
  have eq481 : sK0 ≠ ((sK1 ◇ sK3) ◇ sK0) := superpose eq438 eq10 -- backward demodulation 10,438
  subsumption eq481 eq438


@[equational_result]
theorem Equation2575_implies_Equation769 (G : Type*) [Magma G] (h : Equation2575 G) : Equation769 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK1 ◇ sK3) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1)))) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq13 (X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X2) = X2 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq52 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq14 eq13 -- superposition 13,14, 14 into 13, unify on (0).2 in 14 and (0).1.1 in 13
  have eq62 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X2) = X2 := superpose eq52 eq11 -- backward demodulation 11,52
  have eq75 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = ((X2 ◇ (X3 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq9 eq62 -- superposition 62,9, 9 into 62, unify on (0).2 in 9 and (0).1.1.2.2 in 62
  have eq258 (X0 X1 X2 : G) : (X2 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) := superpose eq75 eq13 -- superposition 13,75, 75 into 13, unify on (0).2 in 75 and (0).1.1 in 13
  have eq394 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq258 eq13 -- superposition 13,258, 258 into 13, unify on (0).2 in 258 and (0).1.1 in 13
  have eq438 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq394 eq9 -- backward demodulation 9,394
  have eq440 (X2 X3 : G) : (X2 ◇ X3) = X3 := superpose eq394 eq13 -- backward demodulation 13,394
  have eq481 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq438 eq10 -- backward demodulation 10,438
  have eq487 : sK0 ≠ (sK1 ◇ sK0) := superpose eq440 eq481 -- backward demodulation 481,440
  subsumption eq487 eq440


@[equational_result]
theorem Equation2579_implies_Equation2720 (G : Type*) [Magma G] (h : Equation2579 G) : Equation2720 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK2 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X4) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq28 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq28 rfl


@[equational_result]
theorem Equation258_implies_Equation263 (G : Type*) [Magma G] (h : Equation258 G) : Equation263 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq13 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq26 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := superpose eq14 eq13 -- superposition 13,14, 14 into 13, unify on (0).2 in 14 and (0).1.1 in 13
  have eq47 : sK0 ≠ sK0 := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation258_implies_Equation2663 (G : Type*) [Magma G] (h : Equation258 G) : Equation2663 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq15 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X2) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).1.1.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1.1 in 25
  have eq195 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X2) ◇ X2) := superpose eq15 eq39 -- superposition 39,15, 15 into 39, unify on (0).2 in 15 and (0).2.1.1.1 in 39
  have eq257 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq57 eq195 -- forward demodulation 195,57
  have eq258 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq257 eq10 -- backward demodulation 10,257
  subsumption eq258 eq9


@[equational_result]
theorem Equation258_implies_Equation2850 (G : Type*) [Magma G] (h : Equation258 G) : Equation2850 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq12 eq9


@[equational_result]
theorem Equation258_implies_Equation3459 (G : Type*) [Magma G] (h : Equation258 G) : Equation3459 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq15 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq29 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X2) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq31 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.2 in 13
  have eq92 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ X0) ◇ X0)) := superpose eq29 eq10 -- superposition 10,29, 29 into 10, unify on (0).2 in 29 and (0).2.2 in 10
  subsumption eq92 eq31


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
theorem Equation2601_implies_Equation2716 (G : Type*) [Magma G] (h : Equation2601 G) : Equation2716 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq23 : sK0 ≠ sK0 := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq23 rfl


@[equational_result]
theorem Equation2601_implies_Equation2821 (G : Type*) [Magma G] (h : Equation2601 G) : Equation2821 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK3 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq22 : sK0 ≠ sK0 := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation2602_implies_Equation1635 (G : Type*) [Magma G] (h : Equation2602 G) : Equation1635 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq20 (X1 X2 X3 : G) : ((X3 ◇ X3) ◇ ((X1 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq30 (X0 : G) : sK0 ≠ ((sK0 ◇ sK0) ◇ ((X0 ◇ X0) ◇ sK0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2.2 in 10
  subsumption eq30 eq20


@[equational_result]
theorem Equation2602_implies_Equation1729 (G : Type*) [Magma G] (h : Equation2602 G) : Equation1729 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq20 (X1 X2 X3 : G) : ((X3 ◇ X3) ◇ ((X1 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq27 (X0 : G) : sK0 ≠ ((sK1 ◇ sK1) ◇ ((X0 ◇ X0) ◇ sK0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2.2 in 10
  subsumption eq27 eq20


@[equational_result]
theorem Equation2602_implies_Equation1740 (G : Type*) [Magma G] (h : Equation2602 G) : Equation1740 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq20 (X1 X2 X3 : G) : ((X3 ◇ X3) ◇ ((X1 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq29 (X0 : G) : sK0 ≠ ((sK1 ◇ sK1) ◇ ((X0 ◇ X0) ◇ sK0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2.2 in 10
  subsumption eq29 eq20


@[equational_result]
theorem Equation2609_implies_Equation283 (G : Type*) [Magma G] (h : Equation2609 G) : Equation283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X2 X3 : G) : (((X2 ◇ X2) ◇ X2) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


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
theorem Equation2623_implies_Equation242 (G : Type*) [Magma G] (h : Equation2623 G) : Equation242 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X4)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation263_implies_Equation2644 (G : Type*) [Magma G] (h : Equation263 G) : Equation2644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.1 in 8
  have eq20 : sK0 ≠ sK0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq20 rfl


@[equational_result]
theorem Equation263_implies_Equation2847 (G : Type*) [Magma G] (h : Equation263 G) : Equation2847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq8


@[equational_result]
theorem Equation263_implies_Equation307 (G : Type*) [Magma G] (h : Equation263 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation2633_implies_Equation2579 (G : Type*) [Magma G] (h : Equation2633 G) : Equation2579 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK0) ◇ sK3)) ◇ sK0) := mod_symm nh
  have eq13 (X3 X4 X5 : G) : (((X3 ◇ X4) ◇ X4) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq26 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq38 : sK0 ≠ ((sK1 ◇ sK3) ◇ sK0) := superpose eq26 eq10 -- backward demodulation 10,26
  subsumption eq38 eq26


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
theorem Equation2649_implies_Equation255 (G : Type*) [Magma G] (h : Equation2649 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation2653_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2653 G) : Equation2035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1 in 8
  have eq13 (X0 X1 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X1 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1.2 in 8
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1.1 in 8
  have eq21 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  have eq24 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq12 eq21 -- forward demodulation 21,12
  have eq25 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq24 eq11 -- backward demodulation 11,24
  have eq37 : sK0 ≠ sK0 := superpose eq25 eq9 -- superposition 9,25, 25 into 9, unify on (0).2 in 25 and (0).2 in 9
  subsumption eq37 rfl


@[equational_result]
theorem Equation2653_implies_Equation255 (G : Type*) [Magma G] (h : Equation2653 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1 in 8
  have eq16 : sK0 ≠ sK0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq16 rfl


@[equational_result]
theorem Equation2653_implies_Equation2875 (G : Type*) [Magma G] (h : Equation2653 G) : Equation2875 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq13 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X1 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.1 in 9
  have eq20 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ X1) := superpose eq11 eq15 -- superposition 15,11, 11 into 15, unify on (0).2 in 11 and (0).1 in 15
  have eq22 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2.1 in 15
  have eq25 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq13 eq22 -- forward demodulation 22,13
  have eq26 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq25 eq12 -- backward demodulation 12,25
  have eq27 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose eq26 eq20 -- backward demodulation 20,26
  have eq30 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq27 eq10 -- backward demodulation 10,27
  subsumption eq30 eq13


@[equational_result]
theorem Equation2653_implies_Equation307 (G : Type*) [Magma G] (h : Equation2653 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1 in 8
  have eq13 (X0 X1 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X1 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1.2 in 8
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1.1 in 8
  have eq15 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq10 eq12 -- superposition 12,10, 10 into 12, unify on (0).2 in 10 and (0).1.1.1 in 12
  have eq21 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  have eq24 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq12 eq21 -- forward demodulation 21,12
  have eq25 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq24 eq11 -- backward demodulation 11,24
  have eq28 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq25 eq15 -- backward demodulation 15,25
  have eq32 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2 in 9
  subsumption eq32 rfl


@[equational_result]
theorem Equation2653_implies_Equation3456 (G : Type*) [Magma G] (h : Equation2653 G) : Equation3456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1 in 8
  have eq13 (X0 X1 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X1 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1.2 in 8
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1.1 in 8
  have eq15 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq10 eq12 -- superposition 12,10, 10 into 12, unify on (0).2 in 10 and (0).1.1.1 in 12
  have eq21 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  have eq24 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq12 eq21 -- forward demodulation 21,12
  have eq25 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq24 eq11 -- backward demodulation 11,24
  have eq28 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq25 eq15 -- backward demodulation 15,25
  have eq33 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq28 eq14 -- superposition 14,28, 28 into 14, unify on (0).2 in 28 and (0).2.1 in 14
  have eq35 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq24 eq33 -- forward demodulation 33,24
  have eq39 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq35 eq9 -- superposition 9,35, 35 into 9, unify on (0).2 in 35 and (0).2 in 9
  subsumption eq39 rfl


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
theorem Equation2655_implies_Equation257 (G : Type*) [Magma G] (h : Equation2655 G) : Equation257 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X3 : G) : (((X3 ◇ X3) ◇ X0) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


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
theorem Equation2658_implies_Equation264 (G : Type*) [Magma G] (h : Equation2658 G) : Equation264 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (((X4 ◇ X4) ◇ X0) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq12


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
theorem Equation2666_implies_Equation3460 (G : Type*) [Magma G] (h : Equation2666 G) : Equation3460 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = (((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X0) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq22 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq23 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) ◇ X1) := superpose eq18 eq11 -- backward demodulation 11,18
  have eq24 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ X3) ◇ X0) ◇ X3) := superpose eq18 eq12 -- backward demodulation 12,18
  have eq35 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq22 eq22 -- superposition 22,22, 22 into 22, unify on (0).2 in 22 and (0).1.1 in 22
  have eq38 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq22 eq23 -- superposition 23,22, 22 into 23, unify on (0).2 in 22 and (0).1 in 23
  have eq39 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq35 eq23 -- superposition 23,35, 35 into 23, unify on (0).2 in 35 and (0).1 in 23
  have eq42 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq18 eq38 -- forward demodulation 38,18
  have eq43 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq18 eq39 -- forward demodulation 39,18
  have eq45 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq22 eq42 -- superposition 42,22, 22 into 42, unify on (0).2 in 22 and (0).1.1 in 42
  have eq46 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq18 eq45 -- forward demodulation 45,18
  have eq51 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq24 eq24 -- superposition 24,24, 24 into 24, unify on (0).2 in 24 and (0).2.1.1 in 24
  have eq54 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ (((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ X2)) := superpose eq23 eq24 -- superposition 24,23, 23 into 24, unify on (0).2 in 23 and (0).2.1 in 24
  have eq60 (X0 X1 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq18 eq51 -- forward demodulation 51,18
  have eq61 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq18 eq60 -- forward demodulation 60,18
  have eq64 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) ◇ X2)) := superpose eq18 eq54 -- forward demodulation 54,18
  have eq65 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X0) ◇ (((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X0) ◇ X2)) := superpose eq18 eq64 -- forward demodulation 64,18
  have eq81 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) = ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) := superpose eq22 eq18 -- superposition 18,22, 22 into 18, unify on (0).2 in 22 and (0).1.1 in 18
  have eq99 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq18 eq22 -- superposition 22,18, 18 into 22, unify on (0).2 in 18 and (0).1.1 in 22
  have eq109 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq18 eq22 -- superposition 22,18, 18 into 22, unify on (0).2 in 18 and (0).1.1.1 in 22
  have eq110 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) := superpose eq18 eq81 -- forward demodulation 81,18
  have eq111 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) := superpose eq22 eq110 -- forward demodulation 110,22
  have eq117 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq111 eq43 -- backward demodulation 43,111
  have eq159 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := superpose eq22 eq99 -- superposition 99,22, 22 into 99, unify on (0).2 in 22 and (0).1.2 in 99
  have eq167 (X0 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2) := superpose eq99 eq18 -- superposition 18,99, 99 into 18, unify on (0).2 in 99 and (0).1.2 in 18
  have eq169 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq109 eq159 -- forward demodulation 159,109
  have eq173 (X0 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ X2) := superpose eq18 eq167 -- forward demodulation 167,18
  have eq174 (X0 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X2) := superpose eq169 eq173 -- forward demodulation 173,169
  have eq175 (X0 X2 : G) : (X0 ◇ X2) = ((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ X0) := superpose eq42 eq174 -- forward demodulation 174,42
  have eq178 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq175 eq65 -- backward demodulation 65,175
  have eq180 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq175 eq61 -- backward demodulation 61,175
  have eq301 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X1))) := superpose eq18 eq117 -- superposition 117,18, 18 into 117, unify on (0).2 in 18 and (0).1.1 in 117
  have eq378 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq178 eq178 -- superposition 178,178, 178 into 178, unify on (0).2 in 178 and (0).2.1 in 178
  have eq441 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) := superpose eq18 eq378 -- forward demodulation 378,18
  have eq533 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq18 eq169 -- superposition 169,18, 18 into 169, unify on (0).2 in 18 and (0).1.1 in 169
  have eq561 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq169 eq18 -- superposition 18,169, 169 into 18, unify on (0).2 in 169 and (0).1.1 in 18
  have eq604 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq169 eq561 -- forward demodulation 561,169
  have eq605 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq533 eq604 -- forward demodulation 604,533
  have eq608 (X0 X1 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) := superpose eq605 eq441 -- backward demodulation 441,605
  have eq610 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq608 eq301 -- backward demodulation 301,608
  have eq1463 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq18 eq109 -- superposition 109,18, 18 into 109, unify on (0).2 in 18 and (0).2.1 in 109
  have eq1547 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq18 eq1463 -- forward demodulation 1463,18
  have eq1776 (X0 X1 X2 : G) : (X0 ◇ (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ X2)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ X2))) := superpose eq111 eq180 -- superposition 180,111, 111 into 180, unify on (0).2 in 111 and (0).2.1 in 180
  have eq1806 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ X2)) := superpose eq1547 eq1776 -- forward demodulation 1776,1547
  have eq1807 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) ◇ X2)) := superpose eq18 eq1806 -- forward demodulation 1806,18
  have eq1808 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X2)) := superpose eq169 eq1807 -- forward demodulation 1807,169
  have eq1809 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) ◇ X2)) := superpose eq610 eq1808 -- forward demodulation 1808,610
  have eq1810 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq22 eq1809 -- forward demodulation 1809,22
  have eq1811 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq46 eq1810 -- forward demodulation 1810,46
  have eq1893 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq1811 eq10 -- superposition 10,1811, 1811 into 10, unify on (0).2 in 1811 and (0).2 in 10
  subsumption eq1893 rfl


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
theorem Equation2683_implies_Equation263 (G : Type*) [Magma G] (h : Equation2683 G) : Equation263 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X3 : G) : (((X3 ◇ X0) ◇ X0) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq21 rfl


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
theorem Equation2687_implies_Equation2662 (G : Type*) [Magma G] (h : Equation2687 G) : Equation2662 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = ((X0 ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq19 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X3 ◇ X3)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X3 ◇ X3))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1 in 11
  have eq20 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X3)) = ((((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X4 ◇ X4)) ◇ (X0 ◇ (X3 ◇ X3))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq42 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ X0) = (((((((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X2)) ◇ X3) ◇ (X4 ◇ X4)) ◇ (X5 ◇ X5)) ◇ (X0 ◇ X0)) := superpose eq9 eq20 -- superposition 20,9, 9 into 20, unify on (0).2 in 9 and (0).1 in 20
  have eq168 (X0 X3 X4 X5 : G) : (X0 ◇ X0) = ((((X0 ◇ (X3 ◇ X3)) ◇ (X4 ◇ X4)) ◇ (X5 ◇ X5)) ◇ (X0 ◇ X0)) := superpose eq20 eq42 -- superposition 42,20, 20 into 42, unify on (0).2 in 20 and (0).2.1.1.1 in 42
  have eq173 (X0 X1 X3 X4 X5 X6 : G) : (X0 ◇ X0) = (((((((X0 ◇ X0) ◇ X1) ◇ X3) ◇ (X4 ◇ X4)) ◇ (X5 ◇ X5)) ◇ (X6 ◇ X6)) ◇ (X0 ◇ X0)) := superpose eq11 eq42 -- superposition 42,11, 11 into 42, unify on (0).2 in 11 and (0).2.1.1.1 in 42
  have eq536 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ X0) = (((((((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X3 ◇ X3)) ◇ (X4 ◇ X4)) ◇ (X5 ◇ X5)) ◇ (X6 ◇ X6)) ◇ (X0 ◇ X0)) := superpose eq19 eq173 -- superposition 173,19, 19 into 173, unify on (0).2 in 19 and (0).2.1.1.1.1 in 173
  have eq5776 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq168 eq536 -- superposition 536,168, 168 into 536, unify on (0).2 in 168 and (0).2.1 in 536
  have eq6083 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq9 eq5776 -- superposition 5776,9, 9 into 5776, unify on (0).2 in 9 and (0).2.1.1 in 5776
  have eq6467 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq6083 eq9 -- superposition 9,6083, 6083 into 9, unify on (0).2 in 6083 and (0).1.1 in 9
  have eq6824 : sK0 ≠ sK0 := superpose eq6467 eq10 -- superposition 10,6467, 6467 into 10, unify on (0).2 in 6467 and (0).2 in 10
  subsumption eq6824 rfl


@[equational_result]
theorem Equation2688_implies_Equation4341 (G : Type*) [Magma G] (h : Equation2688 G) : Equation4341 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq27 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq27 eq12


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
theorem Equation2701_implies_Equation675 (G : Type*) [Magma G] (h : Equation2701 G) : Equation675 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ sK3))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq40 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X3 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ X1))) ◇ X4) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2.2.2 in 11
  have eq63 (X1 X3 X4 : G) : (X1 ◇ X4) = X3 := superpose eq9 eq40 -- forward demodulation 40,9
  have eq103 (X1 X3 : G) : X1 = X3 := superpose eq9 eq63 -- superposition 63,9, 9 into 63, unify on (0).2 in 9 and (0).1 in 63
  have eq131 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq10 -- superposition 10,63, 63 into 10, unify on (0).2 in 63 and (0).2 in 10
  subsumption eq131 eq103


@[equational_result]
theorem Equation2702_implies_Equation2249 (G : Type*) [Magma G] (h : Equation2702 G) : Equation2249 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X1 X3 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation270_implies_Equation2696 (G : Type*) [Magma G] (h : Equation270 G) : Equation2696 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq9


@[equational_result]
theorem Equation2703_implies_Equation187 (G : Type*) [Magma G] (h : Equation2703 G) : Equation187 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = (((X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X3))) ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X3)) ◇ X4))) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq34 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11, 11 into 13, unify on (0).2 in 11 and (0).2.2.1 in 13
  have eq36 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (((X4 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) ◇ X4) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq50 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq13 eq34 -- superposition 34,13, 13 into 34, unify on (0).2 in 13 and (0).2 in 34
  have eq79 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X3)) ◇ X4))) = X0 := superpose eq50 eq24 -- backward demodulation 24,50
  have eq81 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq50 eq79 -- forward demodulation 79,50
  have eq89 (X0 X1 X2 X4 X5 : G) : ((X4 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = (((X5 ◇ ((X4 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X5) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq133 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ X2) = X0 := superpose eq81 eq81 -- superposition 81,81, 81 into 81, unify on (0).2 in 81 and (0).1.2 in 81
  have eq161 (X0 X1 X2 X4 : G) : ((X4 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = X0 := superpose eq133 eq89 -- backward demodulation 89,133
  have eq162 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X4) := superpose eq161 eq36 -- backward demodulation 36,161
  have eq182 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq81 eq162 -- superposition 162,81, 81 into 162, unify on (0).2 in 81 and (0).1 in 162
  have eq206 (X0 : G) : sK0 ≠ ((sK1 ◇ sK2) ◇ X0) := superpose eq162 eq10 -- superposition 10,162, 162 into 10, unify on (0).2 in 162 and (0).2 in 10
  subsumption eq206 eq182


@[equational_result]
theorem Equation2704_implies_Equation69 (G : Type*) [Magma G] (h : Equation2704 G) : Equation69 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq37 (X1 X3 : G) : X1 = X3 := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).1 in 15
  have eq55 (X0 : G) : sK0 ≠ (sK1 ◇ X0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq55 eq37


@[equational_result]
theorem Equation2707_implies_Equation4332 (G : Type*) [Magma G] (h : Equation2707 G) : Equation4332 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq21 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq30 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).1.1 in 21
  have eq49 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2)) := superpose eq12 eq30 -- superposition 30,12, 12 into 30, unify on (0).2 in 12 and (0).1.2.1 in 30
  have eq73 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := superpose eq11 eq49 -- superposition 49,11, 11 into 49, unify on (0).2 in 11 and (0).2.2.1 in 49
  have eq172 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq73 eq10 -- superposition 10,73, 73 into 10, unify on (0).2 in 73 and (0).2 in 10
  subsumption eq172 eq73


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
theorem Equation2712_implies_Equation2243 (G : Type*) [Magma G] (h : Equation2712 G) : Equation2243 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq17 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq33 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1.1.2 in 11
  have eq38 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X1) = X1 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.1.2 in 9
  have eq107 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.1 in 38
  have eq123 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq107 eq10 -- backward demodulation 10,107
  subsumption eq123 eq33


@[equational_result]
theorem Equation2712_implies_Equation2263 (G : Type*) [Magma G] (h : Equation2712 G) : Equation2263 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq17 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq33 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1.1.2 in 11
  have eq38 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X1) = X1 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.1.2 in 9
  have eq107 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.1 in 38
  have eq123 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq107 eq10 -- backward demodulation 10,107
  subsumption eq123 eq33


@[equational_result]
theorem Equation2712_implies_Equation2443 (G : Type*) [Magma G] (h : Equation2712 G) : Equation2443 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq17 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq39 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.1.1 in 9
  have eq243 : sK0 ≠ sK0 := superpose eq39 eq10 -- superposition 10,39, 39 into 10, unify on (0).2 in 39 and (0).2 in 10
  subsumption eq243 rfl


@[equational_result]
theorem Equation2712_implies_Equation2476 (G : Type*) [Magma G] (h : Equation2712 G) : Equation2476 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq17 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq33 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1.1.2 in 11
  have eq69 : sK0 ≠ sK0 := superpose eq33 eq10 -- superposition 10,33, 33 into 10, unify on (0).2 in 33 and (0).2 in 10
  subsumption eq69 rfl


@[equational_result]
theorem Equation2712_implies_Equation3142 (G : Type*) [Magma G] (h : Equation2712 G) : Equation3142 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq17 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq38 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X1) = X1 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.1.2 in 9
  have eq110 : sK0 ≠ sK0 := superpose eq38 eq10 -- superposition 10,38, 38 into 10, unify on (0).2 in 38 and (0).2 in 10
  subsumption eq110 rfl


@[equational_result]
theorem Equation2712_implies_Equation323 (G : Type*) [Magma G] (h : Equation2712 G) : Equation323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq17 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq38 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X1) = X1 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.1.2 in 9
  have eq107 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.1 in 38
  have eq168 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq107 eq10 -- superposition 10,107, 107 into 10, unify on (0).2 in 107 and (0).2 in 10
  subsumption eq168 rfl


@[equational_result]
theorem Equation2713_implies_Equation2788 (G : Type*) [Magma G] (h : Equation2713 G) : Equation2788 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq15 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X4)) ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2.1.1 in 11
  have eq27 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq14 eq11 -- superposition 11,14, 14 into 11, unify on (0).2 in 14 and (0).1.1.2 in 11
  have eq31 (X0 X1 X3 : G) : ((((X0 ◇ X0) ◇ X3) ◇ X1) ◇ (X0 ◇ X0)) = X3 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.1.2 in 9
  have eq49 (X0 X1 X2 X3 : G) : (X1 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))))) = X3 := superpose eq9 eq27 -- superposition 27,9, 9 into 27, unify on (0).2 in 9 and (0).1.1 in 27
  have eq55 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) = ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X4) ◇ (X1 ◇ X1)) := superpose eq11 eq27 -- superposition 27,11, 11 into 27, unify on (0).2 in 11 and (0).1.2.1 in 27
  have eq63 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X3) ◇ X2) ◇ (X0 ◇ X1)) = X3 := superpose eq27 eq9 -- superposition 9,27, 27 into 9, unify on (0).2 in 27 and (0).1.1.2 in 9
  have eq108 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq14 eq31 -- superposition 31,14, 14 into 31, unify on (0).2 in 14 and (0).1.1 in 31
  have eq133 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) = (X1 ◇ X1) := superpose eq108 eq55 -- backward demodulation 55,108
  have eq138 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ ((X0 ◇ X0) ◇ X4)) ◇ (X0 ◇ X0)) := superpose eq133 eq15 -- backward demodulation 15,133
  have eq155 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq108 eq138 -- forward demodulation 138,108
  have eq161 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq155 eq14 -- backward demodulation 14,155
  have eq172 (X0 X1 X3 : G) : (X1 ◇ ((X3 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X0)))) = X3 := superpose eq155 eq49 -- backward demodulation 49,155
  have eq187 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK1) := superpose eq155 eq10 -- backward demodulation 10,155
  have eq193 (X1 X3 : G) : (X1 ◇ (X3 ◇ X3)) = X3 := superpose eq155 eq172 -- forward demodulation 172,155
  have eq196 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq193 eq108 -- backward demodulation 108,193
  have eq208 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq196 eq161 -- backward demodulation 161,196
  have eq216 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq196 eq208 -- forward demodulation 208,196
  have eq219 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = X3 := superpose eq216 eq63 -- backward demodulation 63,216
  have eq225 (X1 X2 X3 : G) : (X2 ◇ X1) = X3 := superpose eq216 eq219 -- forward demodulation 219,216
  subsumption eq187 eq225


@[equational_result]
theorem Equation2716_implies_Equation1025 (G : Type*) [Magma G] (h : Equation2716 G) : Equation1025 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq11 (X1 X3 : G) : ((X1 ◇ (X3 ◇ X1)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X1 X3 : G) : (((X3 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq14 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq25 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1.1 in 12
  have eq37 : sK0 ≠ sK0 := superpose eq25 eq13 -- superposition 13,25, 25 into 13, unify on (0).2 in 25 and (0).2 in 13
  subsumption eq37 rfl


@[equational_result]
theorem Equation2716_implies_Equation1847 (G : Type*) [Magma G] (h : Equation2716 G) : Equation1847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X1 X3 : G) : ((X1 ◇ (X3 ◇ X1)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X1 X3 : G) : (((X3 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq25 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq25 eq11


@[equational_result]
theorem Equation2716_implies_Equation2253 (G : Type*) [Magma G] (h : Equation2716 G) : Equation2253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X1 X3 : G) : ((X1 ◇ (X3 ◇ X1)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X1 X3 : G) : (((X3 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq25 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq25 eq11


@[equational_result]
theorem Equation2716_implies_Equation2476 (G : Type*) [Magma G] (h : Equation2716 G) : Equation2476 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X3 : G) : ((X1 ◇ (X3 ◇ X1)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2716_implies_Equation2567 (G : Type*) [Magma G] (h : Equation2716 G) : Equation2567 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X3 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq30 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq20 eq9 -- superposition 9,20, 20 into 9, unify on (0).2 in 20 and (0).1.1 in 9
  have eq34 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq30 eq10 -- backward demodulation 10,30
  subsumption eq34 eq30


@[equational_result]
theorem Equation2716_implies_Equation3867 (G : Type*) [Magma G] (h : Equation2716 G) : Equation3867 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X3 : G) : ((X1 ◇ (X3 ◇ X1)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X1 X3 : G) : (((X3 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq14 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq25 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1.1 in 12
  have eq37 : sK0 ≠ sK0 := superpose eq25 eq13 -- superposition 13,25, 25 into 13, unify on (0).2 in 25 and (0).2 in 13
  subsumption eq37 rfl


@[equational_result]
theorem Equation2717_implies_Equation688 (G : Type*) [Magma G] (h : Equation2717 G) : Equation688 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK2 ◇ sK0) ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X3 ◇ X0) ◇ X1) ◇ X3) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq27 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq34 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := superpose eq27 eq10 -- backward demodulation 10,27
  have eq41 (X2 X3 : G) : X2 = X3 := superpose eq17 eq17 -- superposition 17,17, 17 into 17, unify on (0).2 in 17 and (0).1 in 17
  have eq54 (X0 X1 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq17 eq34 -- superposition 34,17, 17 into 34, unify on (0).2 in 17 and (0).2.2 in 34
  subsumption eq54 eq41


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
theorem Equation2720_implies_Equation1767 (G : Type*) [Magma G] (h : Equation2720 G) : Equation1767 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK3) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1321 : sK0 ≠ ((sK1 ◇ sK2) ◇ sK0) := superpose eq1217 eq10 -- backward demodulation 10,1217
  subsumption eq1321 eq1260


@[equational_result]
theorem Equation2720_implies_Equation273 (G : Type*) [Magma G] (h : Equation2720 G) : Equation273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2720_implies_Equation2894 (G : Type*) [Magma G] (h : Equation2720 G) : Equation2894 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK3) ◇ sK0) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1321 : sK0 ≠ (sK3 ◇ sK0) := superpose eq1217 eq10 -- backward demodulation 10,1217
  subsumption eq1321 eq1260


@[equational_result]
theorem Equation2720_implies_Equation2905 (G : Type*) [Magma G] (h : Equation2720 G) : Equation2905 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1321 : sK0 ≠ (sK2 ◇ sK0) := superpose eq1217 eq10 -- backward demodulation 10,1217
  subsumption eq1321 eq1260


@[equational_result]
theorem Equation2720_implies_Equation2915 (G : Type*) [Magma G] (h : Equation2720 G) : Equation2915 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1321 : sK0 ≠ (sK2 ◇ sK0) := superpose eq1217 eq10 -- backward demodulation 10,1217
  subsumption eq1321 eq1260


@[equational_result]
theorem Equation2720_implies_Equation2939 (G : Type*) [Magma G] (h : Equation2720 G) : Equation2939 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq209 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = X1 := superpose eq43 eq9 -- superposition 9,43, 43 into 9, unify on (0).2 in 43 and (0).1.1 in 9
  have eq307 : sK0 ≠ sK0 := superpose eq209 eq10 -- superposition 10,209, 209 into 10, unify on (0).2 in 209 and (0).2 in 10
  subsumption eq307 rfl


@[equational_result]
theorem Equation2720_implies_Equation3081 (G : Type*) [Magma G] (h : Equation2720 G) : Equation3081 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 : sK0 ≠ (sK2 ◇ sK0) := superpose eq1217 eq10 -- backward demodulation 10,1217
  have eq1261 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1324 : sK0 ≠ sK0 := superpose eq1261 eq1260 -- superposition 1260,1261, 1261 into 1260, unify on (0).2 in 1261 and (0).2 in 1260
  subsumption eq1324 rfl


@[equational_result]
theorem Equation2720_implies_Equation3130 (G : Type*) [Magma G] (h : Equation2720 G) : Equation3130 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK2) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 : sK0 ≠ (sK2 ◇ sK0) := superpose eq1217 eq10 -- backward demodulation 10,1217
  have eq1261 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1324 : sK0 ≠ sK0 := superpose eq1261 eq1260 -- superposition 1260,1261, 1261 into 1260, unify on (0).2 in 1261 and (0).2 in 1260
  subsumption eq1324 rfl


@[equational_result]
theorem Equation2720_implies_Equation3654 (G : Type*) [Magma G] (h : Equation2720 G) : Equation3654 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK3 ◇ sK4) ◇ sK1)) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).1.1 in 12
  have eq1001 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.2.1 in 99
  have eq1071 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq1001 -- forward demodulation 1001,12
  have eq1131 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq1071 eq1071 -- superposition 1071,1071, 1071 into 1071, unify on (0).2 in 1071 and (0).2.1 in 1071
  have eq1217 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq1131 eq9 -- backward demodulation 9,1131
  have eq1260 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq1217 eq12 -- backward demodulation 12,1217
  have eq1321 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK1) := superpose eq1217 eq10 -- backward demodulation 10,1217
  have eq1324 : sK1 ≠ (sK0 ◇ sK1) := superpose eq1260 eq1321 -- forward demodulation 1321,1260
  subsumption eq1324 eq1260


@[equational_result]
theorem Equation2721_implies_Equation1905 (G : Type*) [Magma G] (h : Equation2721 G) : Equation1905 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq43 (X2 X3 : G) : X2 = X3 := superpose eq16 eq16 -- superposition 16,16, 16 into 16, unify on (0).2 in 16 and (0).1 in 16
  have eq52 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X1 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq52 eq43


@[equational_result]
theorem Equation2724_implies_Equation211 (G : Type*) [Magma G] (h : Equation2724 G) : Equation211 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X3 : G) : ((X1 ◇ (X3 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation2725_implies_Equation1902 (G : Type*) [Magma G] (h : Equation2725 G) : Equation1902 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq37 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = ((X0 ◇ (X3 ◇ X3)) ◇ (X1 ◇ (X4 ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq59 (X0 : G) : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  have eq536 (X1 X2 : G) : sK0 ≠ ((sK1 ◇ (X1 ◇ X1)) ◇ ((sK0 ◇ sK1) ◇ (X2 ◇ X2))) := superpose eq37 eq59 -- superposition 59,37, 37 into 59, unify on (0).2 in 37 and (0).2 in 59
  subsumption eq536 eq11


@[equational_result]
theorem Equation2728_implies_Equation2960 (G : Type*) [Magma G] (h : Equation2728 G) : Equation2960 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X1 X4 X5 : G) : ((X1 ◇ (X4 ◇ X5)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X1 X4 X5 : G) : (((X4 ◇ X5) ◇ X1) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ (X3 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (sK1 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq15 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X0) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq16 (X1 X5 : G) : (X1 ◇ X5) = X5 := superpose eq15 eq12 -- backward demodulation 12,15
  have eq20 : sK0 ≠ sK0 := superpose eq16 eq14 -- superposition 14,16, 16 into 14, unify on (0).2 in 16 and (0).2 in 14
  subsumption eq20 rfl


@[equational_result]
theorem Equation2729_implies_Equation478 (G : Type*) [Magma G] (h : Equation2729 G) : Equation478 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq12 (X1 X4 X5 : G) : (((X4 ◇ X5) ◇ X1) ◇ X4) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = (X2 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq43 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq43 eq17


@[equational_result]
theorem Equation273_implies_Equation2459 (G : Type*) [Magma G] (h : Equation273 G) : Equation2459 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation2737_implies_Equation1832 (G : Type*) [Magma G] (h : Equation2737 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1 in 10
  have eq28 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1 in 8
  have eq34 : sK0 ≠ sK0 := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2 in 9
  subsumption eq34 rfl


@[equational_result]
theorem Equation2753_implies_Equation2601 (G : Type*) [Magma G] (h : Equation2753 G) : Equation2601 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK2) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq19 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq19 eq18


@[equational_result]
theorem Equation277_implies_Equation1087 (G : Type*) [Magma G] (h : Equation277 G) : Equation1087 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X2 X3 : G) : X2 = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq23 (X0 X1 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq23 eq16


@[equational_result]
theorem Equation2771_implies_Equation2775 (G : Type*) [Magma G] (h : Equation2771 G) : Equation2775 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq21 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq29 (X0 : G) : sK0 ≠ (X0 ◇ sK1) := superpose eq16 eq21 -- superposition 21,16, 16 into 21, unify on (0).2 in 16 and (0).2.1 in 21
  subsumption eq29 eq16


@[equational_result]
theorem Equation2772_implies_Equation995 (G : Type*) [Magma G] (h : Equation2772 G) : Equation995 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X1 X2 : G) : X1 = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq20 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq20 eq14


@[equational_result]
theorem Equation2774_implies_Equation2285 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2285 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2774_implies_Equation2300 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2300 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq29 (X0 X1 X4 : G) : ((X1 ◇ (X4 ◇ (X1 ◇ X0))) ◇ X4) = X4 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2.2 in 11
  have eq129 : sK0 ≠ sK0 := superpose eq29 eq10 -- superposition 10,29, 29 into 10, unify on (0).2 in 29 and (0).2 in 10
  subsumption eq129 rfl


@[equational_result]
theorem Equation2774_implies_Equation2303 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2303 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq29 (X0 X1 X4 : G) : ((X1 ◇ (X4 ◇ (X1 ◇ X0))) ◇ X4) = X4 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2.2 in 11
  have eq129 : sK0 ≠ sK0 := superpose eq29 eq10 -- superposition 10,29, 29 into 10, unify on (0).2 in 29 and (0).2 in 10
  subsumption eq129 rfl


@[equational_result]
theorem Equation2774_implies_Equation2306 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2306 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq29 (X0 X1 X4 : G) : ((X1 ◇ (X4 ◇ (X1 ◇ X0))) ◇ X4) = X4 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2.2 in 11
  have eq129 : sK0 ≠ sK0 := superpose eq29 eq10 -- superposition 10,29, 29 into 10, unify on (0).2 in 29 and (0).2 in 10
  subsumption eq129 rfl


@[equational_result]
theorem Equation2775_implies_Equation2382 (G : Type*) [Magma G] (h : Equation2775 G) : Equation2382 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = (((X0 ◇ X3) ◇ X2) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq26 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X2 ◇ X0) ◇ X0)) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq29 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((((X2 ◇ X0) ◇ X4) ◇ (((X0 ◇ X3) ◇ X2) ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq74 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X3) ◇ (((X0 ◇ X2) ◇ X1) ◇ X0)) = X0 := superpose eq12 eq26 -- superposition 26,12, 12 into 26, unify on (0).2 in 12 and (0).1.2 in 26
  have eq90 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X0)) := superpose eq74 eq29 -- backward demodulation 29,74
  have eq99 (X0 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ X2) := superpose eq9 eq90 -- superposition 90,9, 9 into 90, unify on (0).2 in 9 and (0).2.2 in 90
  have eq140 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = X2 := superpose eq26 eq99 -- superposition 99,26, 26 into 99, unify on (0).2 in 26 and (0).1 in 99
  have eq178 (X0 : G) : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0) := superpose eq99 eq10 -- superposition 10,99, 99 into 10, unify on (0).2 in 99 and (0).2 in 10
  subsumption eq178 eq140


@[equational_result]
theorem Equation2778_implies_Equation211 (G : Type*) [Magma G] (h : Equation2778 G) : Equation211 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X2 ◇ (X3 ◇ X2)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = (((X3 ◇ X2) ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X2 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq23 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X2) = (((X4 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq72 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).1 in 14
  have eq73 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.1 in 11
  have eq239 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq73 eq23 -- superposition 23,73, 73 into 23, unify on (0).2 in 73 and (0).2.1 in 23
  have eq713 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq72 eq239 -- superposition 239,72, 72 into 239, unify on (0).2 in 72 and (0).2.1 in 239
  have eq3266 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq713 eq9 -- superposition 9,713, 713 into 9, unify on (0).2 in 713 and (0).1.1 in 9
  have eq3592 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq3266 eq9 -- superposition 9,3266, 3266 into 9, unify on (0).2 in 3266 and (0).1.1 in 9
  have eq3881 : sK0 ≠ sK0 := superpose eq3592 eq10 -- superposition 10,3592, 3592 into 10, unify on (0).2 in 3592 and (0).2 in 10
  subsumption eq3881 rfl


@[equational_result]
theorem Equation2778_implies_Equation221 (G : Type*) [Magma G] (h : Equation2778 G) : Equation221 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X2 ◇ (X3 ◇ X2)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2782_implies_Equation224 (G : Type*) [Magma G] (h : Equation2782 G) : Equation224 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X4 X5 : G) : ((X2 ◇ (X4 ◇ X5)) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation2787_implies_Equation2567 (G : Type*) [Magma G] (h : Equation2787 G) : Equation2567 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq21 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq21 eq14


@[equational_result]
theorem Equation2787_implies_Equation2584 (G : Type*) [Magma G] (h : Equation2787 G) : Equation2584 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq29 (X0 X3 X4 : G) : ((X3 ◇ ((X0 ◇ X3) ◇ X4)) ◇ X4) = X4 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2.1 in 11
  have eq112 : sK0 ≠ sK0 := superpose eq29 eq10 -- superposition 10,29, 29 into 10, unify on (0).2 in 29 and (0).2 in 10
  subsumption eq112 rfl


@[equational_result]
theorem Equation2788_implies_Equation538 (G : Type*) [Magma G] (h : Equation2788 G) : Equation538 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq22 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose eq19 eq9 -- backward demodulation 9,19
  have eq23 (X0 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3)) ◇ (X0 ◇ (X0 ◇ X2))) = X3 := superpose eq19 eq11 -- backward demodulation 11,19
  have eq25 (X0 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq19 eq13 -- backward demodulation 13,19
  have eq30 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq33 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq22 eq22 -- superposition 22,22, 22 into 22, unify on (0).2 in 22 and (0).1.1.2 in 22
  have eq34 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq22 eq33 -- superposition 33,22, 22 into 33, unify on (0).2 in 22 and (0).1.1 in 33
  have eq40 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq34 eq33 -- superposition 33,34, 34 into 33, unify on (0).2 in 34 and (0).1.1.1.2 in 33
  have eq42 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq25 eq40 -- forward demodulation 40,25
  have eq43 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq42 eq34 -- backward demodulation 34,42
  have eq45 (X0 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq43 eq25 -- backward demodulation 25,43
  have eq57 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq43 eq23 -- superposition 23,43, 43 into 23, unify on (0).2 in 43 and (0).1.1.2 in 23
  have eq62 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq45 eq57 -- forward demodulation 57,45
  have eq65 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := superpose eq62 eq30 -- backward demodulation 30,62
  subsumption eq65 eq45


@[equational_result]
theorem Equation2789_implies_Equation1267 (G : Type*) [Magma G] (h : Equation2789 G) : Equation1267 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X4)) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X3)) = X4 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2.1 in 11
  have eq18 (X1 X2 : G) : ((X2 ◇ X2) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq21 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X3)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq40 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X2) ◇ X1) ◇ X2) = X1 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.1.2 in 9
  have eq53 (X1 X2 : G) : ((X2 ◇ X1) ◇ X2) = X1 := superpose eq18 eq40 -- forward demodulation 40,18
  have eq63 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3)) = X2 := superpose eq18 eq21 -- superposition 21,18, 18 into 21, unify on (0).2 in 18 and (0).1.2.1.1 in 21
  have eq73 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0)) = X3 := superpose eq18 eq21 -- superposition 21,18, 18 into 21, unify on (0).2 in 18 and (0).1 in 21
  have eq76 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq21 eq9 -- superposition 9,21, 21 into 9, unify on (0).2 in 21 and (0).1.1 in 9
  have eq86 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ (X4 ◇ X5)) ◇ (X3 ◇ X4)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = ((X2 ◇ X5) ◇ X1) := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1.2 in 11
  have eq87 (X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = X2 := superpose eq18 eq63 -- forward demodulation 63,18
  have eq88 (X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = X2 := superpose eq53 eq87 -- forward demodulation 87,53
  have eq92 (X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ X3)) = X4 := superpose eq76 eq17 -- backward demodulation 17,76
  have eq101 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq92 eq73 -- backward demodulation 73,92
  have eq119 (X0 X1 X2 X5 : G) : ((X2 ◇ X5) ◇ X1) = (X5 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) := superpose eq92 eq86 -- forward demodulation 86,92
  have eq169 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq92 eq53 -- superposition 53,92, 92 into 53, unify on (0).2 in 92 and (0).1.1 in 53
  have eq189 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq88 -- superposition 88,9, 9 into 88, unify on (0).2 in 9 and (0).1.2 in 88
  have eq234 (X1 X2 X5 : G) : ((X2 ◇ X5) ◇ X1) = (X5 ◇ (X1 ◇ X2)) := superpose eq189 eq119 -- backward demodulation 119,189
  have eq253 : sK0 ≠ (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := superpose eq234 eq10 -- backward demodulation 10,234
  have eq304 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq169 eq253 -- forward demodulation 253,169
  subsumption eq304 eq101


@[equational_result]
theorem Equation2789_implies_Equation1387 (G : Type*) [Magma G] (h : Equation2789 G) : Equation1387 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK2) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq18 (X1 X2 : G) : ((X2 ◇ X2) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq22 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq18 eq10 -- backward demodulation 10,18
  have eq24 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X2 := superpose eq18 eq11 -- superposition 11,18, 18 into 11, unify on (0).2 in 18 and (0).1.1.2 in 11
  have eq56 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq18 eq24 -- superposition 24,18, 18 into 24, unify on (0).2 in 18 and (0).1.1 in 24
  have eq57 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq24 eq24 -- superposition 24,24, 24 into 24, unify on (0).2 in 24 and (0).1.1 in 24
  have eq153 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = (X0 ◇ X2) := superpose eq56 eq11 -- superposition 11,56, 56 into 11, unify on (0).2 in 56 and (0).1.1 in 11
  have eq177 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq153 eq9 -- backward demodulation 9,153
  have eq418 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq24 eq177 -- superposition 177,24, 24 into 177, unify on (0).2 in 24 and (0).1.1 in 177
  have eq423 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq418 eq22 -- backward demodulation 22,418
  subsumption eq423 eq57


@[equational_result]
theorem Equation2789_implies_Equation2964 (G : Type*) [Magma G] (h : Equation2789 G) : Equation2964 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ X2) ◇ X3) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X4)) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X3)) = X4 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2.1 in 11
  have eq18 (X1 X2 : G) : ((X2 ◇ X2) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq19 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X3)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq37 (X1 X2 : G) : ((X2 ◇ X1) ◇ X2) = X1 := superpose eq18 eq12 -- superposition 12,18, 18 into 12, unify on (0).2 in 18 and (0).1.1.1 in 12
  have eq63 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3)) = X2 := superpose eq18 eq19 -- superposition 19,18, 18 into 19, unify on (0).2 in 18 and (0).1.2.1.1 in 19
  have eq76 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1 in 9
  have eq79 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ (X4 ◇ X5)) ◇ (X3 ◇ X4)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = ((X2 ◇ X5) ◇ X1) := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.1.2 in 11
  have eq87 (X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = X2 := superpose eq18 eq63 -- forward demodulation 63,18
  have eq88 (X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = X2 := superpose eq37 eq87 -- forward demodulation 87,37
  have eq92 (X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ X3)) = X4 := superpose eq76 eq17 -- backward demodulation 17,76
  have eq113 (X0 X1 X2 X5 : G) : ((X2 ◇ X5) ◇ X1) = (X5 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) := superpose eq92 eq79 -- forward demodulation 79,92
  have eq171 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq92 eq37 -- superposition 37,92, 92 into 37, unify on (0).2 in 92 and (0).1.1 in 37
  have eq189 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq88 -- superposition 88,9, 9 into 88, unify on (0).2 in 9 and (0).1.2 in 88
  have eq234 (X1 X2 X5 : G) : ((X2 ◇ X5) ◇ X1) = (X5 ◇ (X1 ◇ X2)) := superpose eq189 eq113 -- backward demodulation 113,189
  have eq262 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK2 ◇ sK1)) ◇ sK0) := superpose eq234 eq10 -- backward demodulation 10,234
  have eq328 : sK0 ≠ ((sK2 ◇ ((sK2 ◇ sK1) ◇ sK1)) ◇ sK0) := superpose eq234 eq262 -- forward demodulation 262,234
  have eq329 : sK0 ≠ ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ sK0) := superpose eq234 eq328 -- forward demodulation 328,234
  have eq330 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq171 eq329 -- forward demodulation 329,171
  subsumption eq330 eq18


@[equational_result]
theorem Equation2789_implies_Equation647 (G : Type*) [Magma G] (h : Equation2789 G) : Equation647 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X4)) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X3)) = X4 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2.1 in 11
  have eq18 (X1 X2 : G) : ((X2 ◇ X2) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq21 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X3)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq40 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X2) ◇ X1) ◇ X2) = X1 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.1.2 in 9
  have eq53 (X1 X2 : G) : ((X2 ◇ X1) ◇ X2) = X1 := superpose eq18 eq40 -- forward demodulation 40,18
  have eq63 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3)) = X2 := superpose eq18 eq21 -- superposition 21,18, 18 into 21, unify on (0).2 in 18 and (0).1.2.1.1 in 21
  have eq73 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0)) = X3 := superpose eq18 eq21 -- superposition 21,18, 18 into 21, unify on (0).2 in 18 and (0).1 in 21
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq21 eq9 -- superposition 9,21, 21 into 9, unify on (0).2 in 21 and (0).1.1 in 9
  have eq86 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ (X4 ◇ X5)) ◇ (X3 ◇ X4)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = ((X2 ◇ X5) ◇ X1) := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1.2 in 11
  have eq87 (X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = X2 := superpose eq18 eq63 -- forward demodulation 63,18
  have eq88 (X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = X2 := superpose eq53 eq87 -- forward demodulation 87,53
  have eq92 (X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ X3)) = X4 := superpose eq77 eq17 -- backward demodulation 17,77
  have eq101 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq92 eq73 -- backward demodulation 73,92
  have eq119 (X0 X1 X2 X5 : G) : ((X2 ◇ X5) ◇ X1) = (X5 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) := superpose eq92 eq86 -- forward demodulation 86,92
  have eq169 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq92 eq53 -- superposition 53,92, 92 into 53, unify on (0).2 in 92 and (0).1.1 in 53
  have eq189 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq88 -- superposition 88,9, 9 into 88, unify on (0).2 in 9 and (0).1.2 in 88
  have eq234 (X1 X2 X5 : G) : ((X2 ◇ X5) ◇ X1) = (X5 ◇ (X1 ◇ X2)) := superpose eq189 eq119 -- backward demodulation 119,189
  have eq262 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := superpose eq234 eq10 -- backward demodulation 10,234
  have eq328 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq169 eq262 -- forward demodulation 262,169
  subsumption eq328 eq101


@[equational_result]
theorem Equation2789_implies_Equation895 (G : Type*) [Magma G] (h : Equation2789 G) : Equation895 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X4)) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X3)) = X4 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2.1 in 11
  have eq18 (X1 X2 : G) : ((X2 ◇ X2) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq21 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X3)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq40 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X2) ◇ X1) ◇ X2) = X1 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.1.2 in 9
  have eq53 (X1 X2 : G) : ((X2 ◇ X1) ◇ X2) = X1 := superpose eq18 eq40 -- forward demodulation 40,18
  have eq63 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3)) = X2 := superpose eq18 eq21 -- superposition 21,18, 18 into 21, unify on (0).2 in 18 and (0).1.2.1.1 in 21
  have eq76 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq21 eq9 -- superposition 9,21, 21 into 9, unify on (0).2 in 21 and (0).1.1 in 9
  have eq86 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ (X4 ◇ X5)) ◇ (X3 ◇ X4)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = ((X2 ◇ X5) ◇ X1) := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1.2 in 11
  have eq87 (X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = X2 := superpose eq18 eq63 -- forward demodulation 63,18
  have eq88 (X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = X2 := superpose eq53 eq87 -- forward demodulation 87,53
  have eq92 (X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ X3)) = X4 := superpose eq76 eq17 -- backward demodulation 17,76
  have eq119 (X0 X1 X2 X5 : G) : ((X2 ◇ X5) ◇ X1) = (X5 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) := superpose eq92 eq86 -- forward demodulation 86,92
  have eq147 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X1 := superpose eq53 eq92 -- superposition 92,53, 53 into 92, unify on (0).2 in 53 and (0).1.1 in 92
  have eq150 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X0)) ◇ X4)) ◇ X2)) = X3 := superpose eq11 eq92 -- superposition 92,11, 11 into 92, unify on (0).2 in 11 and (0).1.1 in 92
  have eq189 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq88 -- superposition 88,9, 9 into 88, unify on (0).2 in 9 and (0).1.2 in 88
  have eq234 (X1 X2 X5 : G) : ((X2 ◇ X5) ◇ X1) = (X5 ◇ (X1 ◇ X2)) := superpose eq189 eq119 -- backward demodulation 119,189
  have eq240 (X0 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (((X2 ◇ X3) ◇ X0) ◇ X4)) ◇ X2)) = X3 := superpose eq189 eq150 -- backward demodulation 150,189
  have eq248 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := superpose eq234 eq147 -- backward demodulation 147,234
  have eq262 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ sK0))) := superpose eq234 eq10 -- backward demodulation 10,234
  have eq328 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := superpose eq234 eq262 -- forward demodulation 262,234
  have eq337 (X0 X2 X3 X4 : G) : (X4 ◇ ((((X2 ◇ X3) ◇ X0) ◇ X4) ◇ (X2 ◇ X0))) = X3 := superpose eq234 eq240 -- forward demodulation 240,234
  have eq338 (X0 X2 X3 X4 : G) : (X4 ◇ (X4 ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X3) ◇ X0)))) = X3 := superpose eq234 eq337 -- forward demodulation 337,234
  have eq339 (X0 X2 X3 X4 : G) : (X4 ◇ (X4 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X0) ◇ X2)))) = X3 := superpose eq234 eq338 -- forward demodulation 338,234
  have eq340 (X0 X2 X3 X4 : G) : (X4 ◇ (X4 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3)))))) = X3 := superpose eq234 eq339 -- forward demodulation 339,234
  have eq341 (X3 X4 : G) : (X4 ◇ (X4 ◇ X3)) = X3 := superpose eq248 eq340 -- forward demodulation 340,248
  have eq354 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq341 eq328 -- backward demodulation 328,341
  subsumption eq354 eq88


@[equational_result]
theorem Equation2789_implies_Equation898 (G : Type*) [Magma G] (h : Equation2789 G) : Equation898 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK2) ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ X2) ◇ X3) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X4)) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X3)) = X4 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2.1 in 11
  have eq18 (X1 X2 : G) : ((X2 ◇ X2) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq19 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X3)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq26 (X0 X1 X2 X3 X4 X5 : G) : ((((((X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3)) ◇ X4) ◇ X3) ◇ X5) ◇ X2) ◇ X5) = X4 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1.1.2 in 12
  have eq37 (X1 X2 : G) : ((X2 ◇ X1) ◇ X2) = X1 := superpose eq18 eq12 -- superposition 12,18, 18 into 12, unify on (0).2 in 18 and (0).1.1.1 in 12
  have eq63 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3)) = X2 := superpose eq18 eq19 -- superposition 19,18, 18 into 19, unify on (0).2 in 18 and (0).1.2.1.1 in 19
  have eq73 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0)) = X3 := superpose eq18 eq19 -- superposition 19,18, 18 into 19, unify on (0).2 in 18 and (0).1 in 19
  have eq83 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1 in 9
  have eq86 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ (X4 ◇ X5)) ◇ (X3 ◇ X4)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = ((X2 ◇ X5) ◇ X1) := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.1.2 in 11
  have eq87 (X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = X2 := superpose eq18 eq63 -- forward demodulation 63,18
  have eq88 (X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = X2 := superpose eq37 eq87 -- forward demodulation 87,37
  have eq92 (X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ X3)) = X4 := superpose eq83 eq17 -- backward demodulation 17,83
  have eq105 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq92 eq73 -- backward demodulation 73,92
  have eq117 (X0 X1 X2 X5 : G) : ((X2 ◇ X5) ◇ X1) = (X5 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) := superpose eq92 eq86 -- forward demodulation 86,92
  have eq169 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq92 eq37 -- superposition 37,92, 92 into 37, unify on (0).2 in 92 and (0).1.1 in 37
  have eq187 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq88 -- superposition 88,9, 9 into 88, unify on (0).2 in 9 and (0).1.2 in 88
  have eq229 (X0 X2 X3 X4 X5 : G) : ((((((X0 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4) ◇ X3) ◇ X5) ◇ X2) ◇ X5) = X4 := superpose eq187 eq26 -- backward demodulation 26,187
  have eq232 (X1 X2 X5 : G) : ((X2 ◇ X5) ◇ X1) = (X5 ◇ (X1 ◇ X2)) := superpose eq187 eq117 -- backward demodulation 117,187
  have eq242 (X0 X2 X3 X4 X5 : G) : (((X3 ◇ (X5 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4))) ◇ X2) ◇ X5) = X4 := superpose eq232 eq229 -- backward demodulation 229,232
  have eq260 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK2 ◇ sK1) ◇ sK0))) := superpose eq232 eq10 -- backward demodulation 10,232
  have eq276 (X0 X2 X3 X4 X5 : G) : (((X5 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4)) ◇ (X2 ◇ X3)) ◇ X5) = X4 := superpose eq232 eq242 -- forward demodulation 242,232
  have eq277 (X0 X2 X3 X4 X5 : G) : ((((X0 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4) ◇ ((X2 ◇ X3) ◇ X5)) ◇ X5) = X4 := superpose eq232 eq276 -- forward demodulation 276,232
  have eq278 (X0 X2 X3 X4 X5 : G) : ((X4 ◇ (((X2 ◇ X3) ◇ X5) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3)))) ◇ X5) = X4 := superpose eq232 eq277 -- forward demodulation 277,232
  have eq279 (X0 X2 X3 X4 X5 : G) : ((X4 ◇ (X5 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X2 ◇ X3)))) ◇ X5) = X4 := superpose eq232 eq278 -- forward demodulation 278,232
  have eq280 (X0 X2 X3 X4 X5 : G) : ((X4 ◇ (X5 ◇ (((X2 ◇ X0) ◇ X3) ◇ ((X2 ◇ X3) ◇ X0)))) ◇ X5) = X4 := superpose eq232 eq279 -- forward demodulation 279,232
  have eq281 (X0 X2 X3 X4 X5 : G) : ((X4 ◇ (X5 ◇ (X3 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X2 ◇ X0))))) ◇ X5) = X4 := superpose eq232 eq280 -- forward demodulation 280,232
  have eq282 (X0 X2 X3 X4 X5 : G) : ((X4 ◇ (X5 ◇ (X3 ◇ (X0 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X3)))))) ◇ X5) = X4 := superpose eq232 eq281 -- forward demodulation 281,232
  have eq283 (X0 X3 X4 X5 : G) : ((X4 ◇ (X5 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X3))))) ◇ X5) = X4 := superpose eq187 eq282 -- forward demodulation 282,187
  have eq284 (X0 X4 X5 : G) : ((X4 ◇ (X5 ◇ (X0 ◇ X0))) ◇ X5) = X4 := superpose eq169 eq283 -- forward demodulation 283,169
  have eq285 (X4 X5 : G) : ((X4 ◇ X5) ◇ X5) = X4 := superpose eq105 eq284 -- forward demodulation 284,105
  have eq326 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := superpose eq232 eq260 -- forward demodulation 260,232
  have eq327 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq169 eq326 -- forward demodulation 326,169
  have eq387 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq37 eq285 -- superposition 285,37, 37 into 285, unify on (0).2 in 37 and (0).1.1 in 285
  have eq395 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq387 eq327 -- backward demodulation 327,387
  subsumption eq395 eq88


@[equational_result]
theorem Equation2791_implies_Equation2430 (G : Type*) [Magma G] (h : Equation2791 G) : Equation2430 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK3))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ X3) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq53 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X0))) ◇ X3) = X3 := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).1.1.2.2 in 14
  have eq56 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3) = X3 := superpose eq15 eq53 -- forward demodulation 53,15
  have eq99 : sK0 ≠ sK0 := superpose eq56 eq10 -- superposition 10,56, 56 into 10, unify on (0).2 in 56 and (0).2 in 10
  subsumption eq99 rfl


@[equational_result]
theorem Equation280_implies_Equation3659 (G : Type*) [Magma G] (h : Equation280 G) : Equation3659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation2804_implies_Equation228 (G : Type*) [Magma G] (h : Equation2804 G) : Equation228 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2804_implies_Equation270 (G : Type*) [Magma G] (h : Equation2804 G) : Equation270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq17 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq38 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.1.2 in 9
  have eq89 : sK0 ≠ sK0 := superpose eq38 eq10 -- superposition 10,38, 38 into 10, unify on (0).2 in 38 and (0).2 in 10
  subsumption eq89 rfl


@[equational_result]
theorem Equation2806_implies_Equation1351 (G : Type*) [Magma G] (h : Equation2806 G) : Equation1351 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK0) ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X3)) ◇ X1) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 (X1 X2 X3 : G) : (X3 ◇ X1) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq35 (X2 X3 : G) : X2 = X3 := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).1 in 15
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq48 eq35


