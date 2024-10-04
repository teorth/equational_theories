import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation740_implies_Equation1569 (G : Type*) [Magma G] (h : Equation740 G) : Equation1569 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq13 (X1 X2 : G) : ((X1 ◇ X1) ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1 in 13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X0))) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq95 (X0 : G) : sK0 ≠ (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq95 eq19


@[equational_result]
theorem Equation2073_implies_Equation2684 (G : Type*) [Magma G] (h : Equation2073 G) : Equation2684 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq21 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := superpose eq16 eq10 -- backward demodulation 10,16
  have eq28 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq43 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ X0) ◇ sK1) := superpose eq16 eq21 -- superposition 21,16, 16 into 21, unify on (0).2 in 16 and (0).2.1 in 21
  subsumption eq43 eq28


@[equational_result]
theorem Equation2716_implies_Equation3149 (G : Type*) [Magma G] (h : Equation2716 G) : Equation3149 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X1 X3 : G) : ((X1 ◇ (X3 ◇ X1)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X1 X3 : G) : (((X3 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq17 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq25 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).1.1 in 12
  have eq36 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq25 eq9 -- superposition 9,25, 25 into 9, unify on (0).2 in 25 and (0).1.1 in 9
  have eq47 : sK0 ≠ sK0 := superpose eq36 eq17 -- superposition 17,36, 36 into 17, unify on (0).2 in 36 and (0).2 in 17
  subsumption eq47 rfl


@[equational_result]
theorem Equation2716_implies_Equation3715 (G : Type*) [Magma G] (h : Equation2716 G) : Equation3715 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X3 : G) : (((X3 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq25 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq20 eq10 -- backward demodulation 10,20
  have eq26 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq25 -- forward demodulation 25,20
  subsumption eq26 rfl


@[equational_result]
theorem Equation2716_implies_Equation817 (G : Type*) [Magma G] (h : Equation2716 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X1 X3 : G) : (((X3 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq19 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq23 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq19 eq9 -- backward demodulation 9,19
  have eq25 : sK0 ≠ (sK0 ◇ sK0) := superpose eq19 eq23 -- forward demodulation 23,19
  subsumption eq25 eq19


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
theorem Equation2716_implies_Equation2446 (G : Type*) [Magma G] (h : Equation2716 G) : Equation2446 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X3 : G) : ((X1 ◇ (X3 ◇ X1)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


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
theorem Equation2398_implies_Equation228 (G : Type*) [Magma G] (h : Equation2398 G) : Equation228 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq22 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation2398_implies_Equation2567 (G : Type*) [Magma G] (h : Equation2398 G) : Equation2567 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq13 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation608_implies_Equation4243 (G : Type*) [Magma G] (h : Equation608 G) : Equation4243 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK3) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X3 X4 X5 : G) : (X3 ◇ X4) = (X5 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ (((X0 ◇ sK3) ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation608_implies_Equation4631 (G : Type*) [Magma G] (h : Equation608 G) : Equation4631 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq13 (X3 X4 X5 : G) : (X3 ◇ X4) = (X5 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ ((X0 ◇ sK2) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation608_implies_Equation4599 (G : Type*) [Magma G] (h : Equation608 G) : Equation4599 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X3 X4 X5 : G) : (X3 ◇ X4) = (X5 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((X0 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation608_implies_Equation4070 (G : Type*) [Magma G] (h : Equation608 G) : Equation4070 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X3 X4 X5 : G) : (X3 ◇ X4) = (X5 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 : G) : (sK0 ◇ sK0) ≠ (((X0 ◇ sK1) ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation978_implies_Equation2441 (G : Type*) [Magma G] (h : Equation978 G) : Equation2441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X3) ◇ X2)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2.1 in 11
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1))) = X0 := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.2.2 in 8
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.2 in 8
  have eq24 (X0 X3 : G) : (X0 ◇ (X3 ◇ X3)) = X0 := superpose eq20 eq19 -- backward demodulation 19,20
  have eq35 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X3) ◇ X1) = (((X4 ◇ X4) ◇ X2) ◇ ((X5 ◇ X5) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2)))) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1.2 in 10
  have eq53 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ ((X3 ◇ X3) ◇ X0)) = X0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).1.1.2 in 10
  have eq68 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ X0)) = X0 := superpose eq24 eq53 -- forward demodulation 53,24
  have eq69 (X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ X1) = (((X4 ◇ X4) ◇ X2) ◇ (X1 ◇ X2)) := superpose eq68 eq35 -- backward demodulation 35,68
  have eq265 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ X0) = (((X4 ◇ X4) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) ◇ X2) := superpose eq8 eq69 -- superposition 69,8, 8 into 69, unify on (0).2 in 8 and (0).2.2 in 69
  have eq340 (X0 X2 X3 : G) : ((X3 ◇ X3) ◇ X0) = ((X2 ◇ X0) ◇ X2) := superpose eq68 eq265 -- forward demodulation 265,68
  have eq1049 (X0 : G) : sK0 ≠ ((X0 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := superpose eq340 eq9 -- superposition 9,340, 340 into 9, unify on (0).2 in 340 and (0).2 in 9
  subsumption eq1049 eq68


@[equational_result]
theorem Equation978_implies_Equation2576 (G : Type*) [Magma G] (h : Equation978 G) : Equation2576 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK0) ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X3) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq20 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq21 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq25 (X0 X3 : G) : (X0 ◇ (X3 ◇ X3)) = X0 := superpose eq21 eq20 -- backward demodulation 20,21
  have eq35 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = (((X3 ◇ X3) ◇ X2) ◇ ((X4 ◇ X4) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq36 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X3) ◇ X1) = (((X4 ◇ X4) ◇ X2) ◇ ((X5 ◇ X5) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq54 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ ((X3 ◇ X3) ◇ X0)) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.1.2 in 11
  have eq67 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ X0)) = X0 := superpose eq25 eq54 -- forward demodulation 54,25
  have eq68 (X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ X1) = (((X4 ◇ X4) ◇ X2) ◇ (X1 ◇ X2)) := superpose eq67 eq36 -- backward demodulation 36,67
  have eq318 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ X0) = (((X4 ◇ X4) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) ◇ X2) := superpose eq9 eq68 -- superposition 68,9, 9 into 68, unify on (0).2 in 9 and (0).2.2 in 68
  have eq400 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X3) ◇ X0) := superpose eq67 eq318 -- forward demodulation 318,67
  have eq686 (X1 X2 X4 : G) : ((X4 ◇ X4) ◇ ((X1 ◇ X2) ◇ X1)) = X2 := superpose eq11 eq35 -- superposition 35,11, 11 into 35, unify on (0).2 in 11 and (0).2 in 35
  have eq971 (X0 : G) : sK0 ≠ ((X0 ◇ X0) ◇ ((sK2 ◇ sK0) ◇ sK2)) := superpose eq400 eq10 -- superposition 10,400, 400 into 10, unify on (0).2 in 400 and (0).2 in 10
  subsumption eq971 eq686


@[equational_result]
theorem Equation978_implies_Equation4620 (G : Type*) [Magma G] (h : Equation978 G) : Equation4620 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X3) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq19 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq21 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq25 (X0 X3 : G) : (X0 ◇ (X3 ◇ X3)) = X0 := superpose eq19 eq21 -- forward demodulation 21,19
  have eq28 (X0 X1 X3 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq25 eq16 -- backward demodulation 16,25
  have eq36 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X3) ◇ X1) = (((X4 ◇ X4) ◇ X2) ◇ ((X5 ◇ X5) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq39 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ (((X1 ◇ X1) ◇ X0) ◇ X3)) ◇ X0) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq51 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.1 in 11
  have eq67 (X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ X1) = (((X4 ◇ X4) ◇ X2) ◇ (X1 ◇ X2)) := superpose eq51 eq36 -- backward demodulation 36,51
  have eq178 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ X1) = (((X4 ◇ X4) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3))) ◇ X1) := superpose eq28 eq39 -- superposition 39,28, 28 into 39, unify on (0).2 in 28 and (0).1.1.2 in 39
  have eq210 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X1) = ((X3 ◇ X3) ◇ X1) := superpose eq51 eq178 -- forward demodulation 178,51
  have eq318 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ X0) = (((X4 ◇ X4) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) ◇ X2) := superpose eq9 eq67 -- superposition 67,9, 9 into 67, unify on (0).2 in 9 and (0).2.2 in 67
  have eq400 (X0 X2 X3 : G) : ((X3 ◇ X3) ◇ X0) = ((X2 ◇ X0) ◇ X2) := superpose eq51 eq318 -- forward demodulation 318,51
  have eq1017 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((X0 ◇ X0) ◇ sK1) := superpose eq400 eq10 -- superposition 10,400, 400 into 10, unify on (0).2 in 400 and (0).2 in 10
  subsumption eq1017 eq210


@[equational_result]
theorem Equation978_implies_Equation1637 (G : Type*) [Magma G] (h : Equation978 G) : Equation1637 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X3) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq20 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq21 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq25 (X0 X3 : G) : (X0 ◇ (X3 ◇ X3)) = X0 := superpose eq21 eq20 -- backward demodulation 20,21
  have eq54 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ ((X3 ◇ X3) ◇ X0)) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.1.2 in 11
  have eq59 (X0 : G) : sK0 ≠ ((X0 ◇ X0) ◇ ((sK1 ◇ sK1) ◇ sK0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  have eq71 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ X0)) = X0 := superpose eq25 eq54 -- forward demodulation 54,25
  subsumption eq59 eq71


@[equational_result]
theorem Equation978_implies_Equation2541 (G : Type*) [Magma G] (h : Equation978 G) : Equation2541 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X3) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq36 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X3) ◇ X1) = (((X4 ◇ X4) ◇ X2) ◇ ((X5 ◇ X5) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq52 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.1 in 11
  have eq69 (X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ X1) = (((X4 ◇ X4) ◇ X2) ◇ (X1 ◇ X2)) := superpose eq52 eq36 -- backward demodulation 36,52
  have eq266 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ X0) = (((X4 ◇ X4) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) ◇ X2) := superpose eq9 eq69 -- superposition 69,9, 9 into 69, unify on (0).2 in 9 and (0).2.2 in 69
  have eq341 (X0 X2 X3 : G) : ((X3 ◇ X3) ◇ X0) = ((X2 ◇ X0) ◇ X2) := superpose eq52 eq266 -- forward demodulation 266,52
  have eq1024 (X0 : G) : sK0 ≠ ((X0 ◇ X0) ◇ ((sK1 ◇ sK1) ◇ sK0)) := superpose eq341 eq10 -- superposition 10,341, 341 into 10, unify on (0).2 in 341 and (0).2 in 10
  subsumption eq1024 eq52


@[equational_result]
theorem Equation978_implies_Equation4647 (G : Type*) [Magma G] (h : Equation978 G) : Equation4647 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK2 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X3) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq36 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X3) ◇ X1) = (((X4 ◇ X4) ◇ X2) ◇ ((X5 ◇ X5) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq51 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.1 in 11
  have eq67 (X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ X1) = (((X4 ◇ X4) ◇ X2) ◇ (X1 ◇ X2)) := superpose eq51 eq36 -- backward demodulation 36,51
  have eq318 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ X0) = (((X4 ◇ X4) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) ◇ X2) := superpose eq9 eq67 -- superposition 67,9, 9 into 67, unify on (0).2 in 9 and (0).2.2 in 67
  have eq400 (X0 X2 X3 : G) : ((X3 ◇ X3) ◇ X0) = ((X2 ◇ X0) ◇ X2) := superpose eq51 eq318 -- forward demodulation 318,51
  have eq1017 (X0 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK1) := superpose eq400 eq10 -- superposition 10,400, 400 into 10, unify on (0).2 in 400 and (0).2 in 10
  subsumption eq1017 eq400


@[equational_result]
theorem Equation978_implies_Equation1075 (G : Type*) [Magma G] (h : Equation978 G) : Equation1075 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X3) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq20 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq21 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq25 (X0 X3 : G) : (X0 ◇ (X3 ◇ X3)) = X0 := superpose eq21 eq20 -- backward demodulation 20,21
  have eq36 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X3) ◇ X1) = (((X4 ◇ X4) ◇ X2) ◇ ((X5 ◇ X5) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq54 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ ((X3 ◇ X3) ◇ X0)) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.1.2 in 11
  have eq67 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ X0)) = X0 := superpose eq25 eq54 -- forward demodulation 54,25
  have eq68 (X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ X1) = (((X4 ◇ X4) ◇ X2) ◇ (X1 ◇ X2)) := superpose eq67 eq36 -- backward demodulation 36,67
  have eq318 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ X0) = (((X4 ◇ X4) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) ◇ X2) := superpose eq9 eq68 -- superposition 68,9, 9 into 68, unify on (0).2 in 9 and (0).2.2 in 68
  have eq400 (X0 X2 X3 : G) : ((X3 ◇ X3) ◇ X0) = ((X2 ◇ X0) ◇ X2) := superpose eq67 eq318 -- forward demodulation 318,67
  have eq1017 (X0 : G) : sK0 ≠ (sK1 ◇ ((X0 ◇ X0) ◇ (sK0 ◇ sK1))) := superpose eq400 eq10 -- superposition 10,400, 400 into 10, unify on (0).2 in 400 and (0).2.2 in 10
  subsumption eq1017 eq9


@[equational_result]
theorem Equation978_implies_Equation2602 (G : Type*) [Magma G] (h : Equation978 G) : Equation2602 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK2) ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X3) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq20 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq21 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq25 (X0 X3 : G) : (X0 ◇ (X3 ◇ X3)) = X0 := superpose eq21 eq20 -- backward demodulation 20,21
  have eq36 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X3) ◇ X1) = (((X4 ◇ X4) ◇ X2) ◇ ((X5 ◇ X5) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq54 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ ((X3 ◇ X3) ◇ X0)) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.1.2 in 11
  have eq69 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ X0)) = X0 := superpose eq25 eq54 -- forward demodulation 54,25
  have eq70 (X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ X1) = (((X4 ◇ X4) ◇ X2) ◇ (X1 ◇ X2)) := superpose eq69 eq36 -- backward demodulation 36,69
  have eq266 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ X0) = (((X4 ◇ X4) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) ◇ X2) := superpose eq9 eq70 -- superposition 70,9, 9 into 70, unify on (0).2 in 9 and (0).2.2 in 70
  have eq341 (X0 X2 X3 : G) : ((X3 ◇ X3) ◇ X0) = ((X2 ◇ X0) ◇ X2) := superpose eq69 eq266 -- forward demodulation 266,69
  have eq1045 (X0 : G) : sK0 ≠ ((X0 ◇ X0) ◇ ((sK2 ◇ sK2) ◇ sK0)) := superpose eq341 eq10 -- superposition 10,341, 341 into 10, unify on (0).2 in 341 and (0).2 in 10
  subsumption eq1045 eq69


@[equational_result]
theorem Equation978_implies_Equation1731 (G : Type*) [Magma G] (h : Equation978 G) : Equation1731 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X3) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq51 (X0 : G) : sK0 ≠ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ sK0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  have eq226 : sK0 ≠ sK0 := superpose eq11 eq51 -- superposition 51,11, 11 into 51, unify on (0).2 in 11 and (0).2 in 51
  subsumption eq226 rfl


@[equational_result]
theorem Equation978_implies_Equation2466 (G : Type*) [Magma G] (h : Equation978 G) : Equation2466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X3) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq20 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq21 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq25 (X0 X3 : G) : (X0 ◇ (X3 ◇ X3)) = X0 := superpose eq21 eq20 -- backward demodulation 20,21
  have eq36 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X3) ◇ X1) = (((X4 ◇ X4) ◇ X2) ◇ ((X5 ◇ X5) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq54 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ ((X3 ◇ X3) ◇ X0)) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.1.2 in 11
  have eq69 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ X0)) = X0 := superpose eq25 eq54 -- forward demodulation 54,25
  have eq70 (X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ X1) = (((X4 ◇ X4) ◇ X2) ◇ (X1 ◇ X2)) := superpose eq69 eq36 -- backward demodulation 36,69
  have eq266 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ X0) = (((X4 ◇ X4) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) ◇ X2) := superpose eq9 eq70 -- superposition 70,9, 9 into 70, unify on (0).2 in 9 and (0).2.2 in 70
  have eq341 (X0 X2 X3 : G) : ((X3 ◇ X3) ◇ X0) = ((X2 ◇ X0) ◇ X2) := superpose eq69 eq266 -- forward demodulation 266,69
  have eq1044 (X0 : G) : sK0 ≠ ((X0 ◇ X0) ◇ ((sK1 ◇ sK1) ◇ sK0)) := superpose eq341 eq10 -- superposition 10,341, 341 into 10, unify on (0).2 in 341 and (0).2 in 10
  subsumption eq1044 eq69


@[equational_result]
theorem Equation978_implies_Equation4598 (G : Type*) [Magma G] (h : Equation978 G) : Equation4598 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X3) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq19 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq21 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq25 (X0 X3 : G) : (X0 ◇ (X3 ◇ X3)) = X0 := superpose eq19 eq21 -- forward demodulation 21,19
  have eq28 (X0 X1 X3 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq25 eq16 -- backward demodulation 16,25
  have eq36 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X3) ◇ X1) = (((X4 ◇ X4) ◇ X2) ◇ ((X5 ◇ X5) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq39 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ (((X1 ◇ X1) ◇ X0) ◇ X3)) ◇ X0) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq51 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.1 in 11
  have eq67 (X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ X1) = (((X4 ◇ X4) ◇ X2) ◇ (X1 ◇ X2)) := superpose eq51 eq36 -- backward demodulation 36,51
  have eq178 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ X1) = (((X4 ◇ X4) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3))) ◇ X1) := superpose eq28 eq39 -- superposition 39,28, 28 into 39, unify on (0).2 in 28 and (0).1.1.2 in 39
  have eq210 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X1) = ((X3 ◇ X3) ◇ X1) := superpose eq51 eq178 -- forward demodulation 178,51
  have eq318 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ X0) = (((X4 ◇ X4) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) ◇ X2) := superpose eq9 eq67 -- superposition 67,9, 9 into 67, unify on (0).2 in 9 and (0).2.2 in 67
  have eq400 (X0 X2 X3 : G) : ((X3 ◇ X3) ◇ X0) = ((X2 ◇ X0) ◇ X2) := superpose eq51 eq318 -- forward demodulation 318,51
  have eq1017 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((X0 ◇ X0) ◇ sK1) := superpose eq400 eq10 -- superposition 10,400, 400 into 10, unify on (0).2 in 400 and (0).2 in 10
  subsumption eq1017 eq210


@[equational_result]
theorem Equation978_implies_Equation1746 (G : Type*) [Magma G] (h : Equation978 G) : Equation1746 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X3) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq20 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq21 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq25 (X0 X3 : G) : (X0 ◇ (X3 ◇ X3)) = X0 := superpose eq21 eq20 -- backward demodulation 20,21
  have eq54 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ ((X3 ◇ X3) ◇ X0)) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.1.2 in 11
  have eq59 (X0 : G) : sK0 ≠ ((X0 ◇ X0) ◇ ((sK2 ◇ sK2) ◇ sK0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  have eq71 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ X0)) = X0 := superpose eq25 eq54 -- forward demodulation 54,25
  subsumption eq59 eq71


@[equational_result]
theorem Equation709_implies_Equation1539 (G : Type*) [Magma G] (h : Equation709 G) : Equation1539 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq29 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1 in 16
  have eq45 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq45 eq29


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
theorem Equation2874_implies_Equation2884 (G : Type*) [Magma G] (h : Equation2874 G) : Equation2884 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X2) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation3082_implies_Equation4673 (G : Type*) [Magma G] (h : Equation3082 G) : Equation4673 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X1) = ((X0 ◇ X3) ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((((X0 ◇ X2) ◇ X2) ◇ X2) ◇ X3) ◇ X2) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1.1 in 9
  have eq69 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = ((((X0 ◇ X1) ◇ X1) ◇ X4) ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq126 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq69 -- forward demodulation 69,9
  have eq127 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq126 eq29 -- backward demodulation 29,126
  have eq135 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X2) = ((X0 ◇ X1) ◇ X4) := superpose eq18 eq127 -- superposition 127,18, 18 into 127, unify on (0).2 in 18 and (0).1 in 127
  have eq167 (X0 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ X0) := superpose eq127 eq13 -- superposition 13,127, 127 into 13, unify on (0).2 in 127 and (0).1 in 13
  subsumption eq167 eq135


@[equational_result]
theorem Equation3082_implies_Equation3055 (G : Type*) [Magma G] (h : Equation3082 G) : Equation3055 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq9


@[equational_result]
theorem Equation3082_implies_Equation4672 (G : Type*) [Magma G] (h : Equation3082 G) : Equation4672 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK1) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq28 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((((X0 ◇ X2) ◇ X2) ◇ X2) ◇ X3) ◇ X2) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1.1 in 9
  have eq30 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = ((((X0 ◇ X1) ◇ X1) ◇ X4) ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq69 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq30 -- forward demodulation 30,9
  have eq70 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq69 eq28 -- backward demodulation 28,69
  have eq93 (X0 : G) : ((sK0 ◇ X0) ◇ sK2) ≠ ((sK0 ◇ X0) ◇ sK3) := superpose eq70 eq10 -- superposition 10,70, 70 into 10, unify on (0).2 in 70 and (0).1.1 in 10
  subsumption eq93 eq70


@[equational_result]
theorem Equation3082_implies_Equation3084 (G : Type*) [Magma G] (h : Equation3082 G) : Equation3084 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq31 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = ((((X0 ◇ X1) ◇ X1) ◇ X4) ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq58 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X3) ◇ X1) ◇ X2) = ((((X0 ◇ X1) ◇ X1) ◇ X4) ◇ X2) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1 in 12
  have eq62 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK1) ◇ X0) ◇ sK1) ◇ sK3) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2.1 in 10
  have eq71 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq31 -- forward demodulation 31,9
  have eq76 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X3) ◇ X1) ◇ X2) = X0 := superpose eq71 eq58 -- forward demodulation 58,71
  subsumption eq62 eq76


@[equational_result]
theorem Equation3082_implies_Equation3465 (G : Type*) [Magma G] (h : Equation3082 G) : Equation3465 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq28 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((((X0 ◇ X2) ◇ X2) ◇ X2) ◇ X3) ◇ X2) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1.1 in 9
  have eq31 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = ((((X0 ◇ X1) ◇ X1) ◇ X4) ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq70 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq31 -- forward demodulation 31,9
  have eq71 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq70 eq28 -- backward demodulation 28,70
  have eq107 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq71 eq10 -- superposition 10,71, 71 into 10, unify on (0).2 in 71 and (0).2 in 10
  subsumption eq107 eq71


@[equational_result]
theorem Equation3082_implies_Equation326 (G : Type*) [Magma G] (h : Equation3082 G) : Equation326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq28 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((((X0 ◇ X2) ◇ X2) ◇ X2) ◇ X3) ◇ X2) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1.1 in 9
  have eq30 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = ((((X0 ◇ X1) ◇ X1) ◇ X4) ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq69 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq30 -- forward demodulation 30,9
  have eq70 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq69 eq28 -- backward demodulation 28,69
  have eq106 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ X0) := superpose eq70 eq10 -- superposition 10,70, 70 into 10, unify on (0).2 in 70 and (0).2 in 10
  subsumption eq106 eq70


@[equational_result]
theorem Equation3082_implies_Equation3469 (G : Type*) [Magma G] (h : Equation3082 G) : Equation3469 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq28 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((((X0 ◇ X2) ◇ X2) ◇ X2) ◇ X3) ◇ X2) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1.1 in 9
  have eq31 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = ((((X0 ◇ X1) ◇ X1) ◇ X4) ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq70 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq31 -- forward demodulation 31,9
  have eq71 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq70 eq28 -- backward demodulation 28,70
  have eq107 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq71 eq10 -- superposition 10,71, 71 into 10, unify on (0).2 in 71 and (0).2 in 10
  subsumption eq107 eq71


@[equational_result]
theorem Equation3082_implies_Equation4357 (G : Type*) [Magma G] (h : Equation3082 G) : Equation4357 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq28 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((((X0 ◇ X2) ◇ X2) ◇ X2) ◇ X3) ◇ X2) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1.1 in 9
  have eq30 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = ((((X0 ◇ X1) ◇ X1) ◇ X4) ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq69 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq30 -- forward demodulation 30,9
  have eq70 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq69 eq28 -- backward demodulation 28,69
  have eq106 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ X0) := superpose eq70 eq10 -- superposition 10,70, 70 into 10, unify on (0).2 in 70 and (0).2 in 10
  subsumption eq106 eq70


@[equational_result]
theorem Equation3086_implies_Equation3060 (G : Type*) [Magma G] (h : Equation3086 G) : Equation3060 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq30 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ X1) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq36 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq30 eq30 -- superposition 30,30, 30 into 30, unify on (0).2 in 30 and (0).1.1 in 30
  have eq54 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X0) ◇ X0) := superpose eq36 eq12 -- backward demodulation 12,36
  have eq67 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK1) ◇ sK2) := superpose eq54 eq10 -- backward demodulation 10,54
  have eq84 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq36 eq36 -- superposition 36,36, 36 into 36, unify on (0).2 in 36 and (0).2 in 36
  have eq159 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq84 eq30 -- superposition 30,84, 84 into 30, unify on (0).2 in 84 and (0).1.1 in 30
  have eq167 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ X0) ◇ sK2) := superpose eq84 eq67 -- superposition 67,84, 84 into 67, unify on (0).2 in 84 and (0).2.1 in 67
  subsumption eq167 eq159


@[equational_result]
theorem Equation59_implies_Equation4510 (G : Type*) [Magma G] (h : Equation59 G) : Equation4510 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq15 -- forward demodulation 15,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation59_implies_Equation2067 (G : Type*) [Magma G] (h : Equation59 G) : Equation2067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq17 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq14 eq16 -- forward demodulation 16,14
  have eq18 : sK0 ≠ (sK0 ◇ sK2) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation59_implies_Equation1053 (G : Type*) [Magma G] (h : Equation59 G) : Equation1053 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq14


@[equational_result]
theorem Equation59_implies_Equation4400 (G : Type*) [Magma G] (h : Equation59 G) : Equation4400 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 : sK0 ≠ (sK0 ◇ sK2) := superpose eq14 eq15 -- forward demodulation 15,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation59_implies_Equation1056 (G : Type*) [Magma G] (h : Equation59 G) : Equation1056 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq14


@[equational_result]
theorem Equation59_implies_Equation1856 (G : Type*) [Magma G] (h : Equation59 G) : Equation1856 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK3)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq14


@[equational_result]
theorem Equation59_implies_Equation379 (G : Type*) [Magma G] (h : Equation59 G) : Equation379 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ (sK0 ◇ sK2) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq15 eq14


@[equational_result]
theorem Equation59_implies_Equation3947 (G : Type*) [Magma G] (h : Equation59 G) : Equation3947 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK3)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 rfl


@[equational_result]
theorem Equation3108_implies_Equation1664 (G : Type*) [Magma G] (h : Equation3108 G) : Equation1664 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq27 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq22 eq10 -- backward demodulation 10,22
  subsumption eq27 eq12


@[equational_result]
theorem Equation3108_implies_Equation2443 (G : Type*) [Magma G] (h : Equation3108 G) : Equation2443 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq12


@[equational_result]
theorem Equation3108_implies_Equation2285 (G : Type*) [Magma G] (h : Equation3108 G) : Equation2285 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq23 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq23 rfl


@[equational_result]
theorem Equation3108_implies_Equation2300 (G : Type*) [Magma G] (h : Equation3108 G) : Equation2300 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.1 in 12
  have eq32 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq31 eq10 -- backward demodulation 10,31
  have eq33 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq19 eq32 -- forward demodulation 32,19
  subsumption eq33 eq22


@[equational_result]
theorem Equation3108_implies_Equation3309 (G : Type*) [Magma G] (h : Equation3108 G) : Equation3309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq39 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq39 rfl


@[equational_result]
theorem Equation3108_implies_Equation4320 (G : Type*) [Magma G] (h : Equation3108 G) : Equation4320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK1 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.1 in 12
  have eq47 : (sK1 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq32 eq15 -- superposition 15,32, 32 into 15, unify on (0).2 in 32 and (0).2 in 15
  subsumption eq47 rfl


@[equational_result]
theorem Equation3108_implies_Equation4284 (G : Type*) [Magma G] (h : Equation3108 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq39 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq39 rfl


@[equational_result]
theorem Equation3108_implies_Equation221 (G : Type*) [Magma G] (h : Equation3108 G) : Equation221 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.1 in 12
  have eq32 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq31 eq10 -- backward demodulation 10,31
  subsumption eq32 eq12


@[equational_result]
theorem Equation3108_implies_Equation4382 (G : Type*) [Magma G] (h : Equation3108 G) : Equation4382 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq14 -- backward demodulation 14,13
  subsumption eq16 eq13


@[equational_result]
theorem Equation3108_implies_Equation2655 (G : Type*) [Magma G] (h : Equation3108 G) : Equation2655 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq12


@[equational_result]
theorem Equation3108_implies_Equation228 (G : Type*) [Magma G] (h : Equation3108 G) : Equation228 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq24 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq32 : sK0 ≠ sK0 := superpose eq22 eq24 -- superposition 24,22, 22 into 24, unify on (0).2 in 22 and (0).2 in 24
  subsumption eq32 rfl


@[equational_result]
theorem Equation3108_implies_Equation2736 (G : Type*) [Magma G] (h : Equation3108 G) : Equation2736 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq24 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq24 eq12 -- superposition 12,24, 24 into 12, unify on (0).2 in 24 and (0).1.1 in 12
  have eq33 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq32 eq15 -- backward demodulation 15,32
  subsumption eq33 eq12


@[equational_result]
theorem Equation3108_implies_Equation3759 (G : Type*) [Magma G] (h : Equation3108 G) : Equation3759 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq24 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq24 eq12 -- superposition 12,24, 24 into 12, unify on (0).2 in 24 and (0).1.1 in 12
  have eq44 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq15 -- superposition 15,32, 32 into 15, unify on (0).2 in 32 and (0).2 in 15
  subsumption eq44 rfl


@[equational_result]
theorem Equation3108_implies_Equation4067 (G : Type*) [Magma G] (h : Equation3108 G) : Equation4067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X1 X3 : G) : (((X1 ◇ X1) ◇ X3) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation3108_implies_Equation2330 (G : Type*) [Magma G] (h : Equation3108 G) : Equation2330 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq24 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.1 in 12
  have eq33 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq32 eq24 -- backward demodulation 24,32
  subsumption eq33 eq12


@[equational_result]
theorem Equation3108_implies_Equation2503 (G : Type*) [Magma G] (h : Equation3108 G) : Equation2503 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq23 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq32 : sK0 ≠ sK0 := superpose eq23 eq14 -- superposition 14,23, 23 into 14, unify on (0).2 in 23 and (0).2 in 14
  subsumption eq32 rfl


@[equational_result]
theorem Equation3108_implies_Equation1837 (G : Type*) [Magma G] (h : Equation3108 G) : Equation1837 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq12


@[equational_result]
theorem Equation3108_implies_Equation1847 (G : Type*) [Magma G] (h : Equation3108 G) : Equation1847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq12


@[equational_result]
theorem Equation3108_implies_Equation1038 (G : Type*) [Magma G] (h : Equation3108 G) : Equation1038 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.1 in 12
  have eq32 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := superpose eq31 eq10 -- backward demodulation 10,31
  have eq33 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq32 -- forward demodulation 32,12
  subsumption eq33 eq13


@[equational_result]
theorem Equation3108_implies_Equation2293 (G : Type*) [Magma G] (h : Equation3108 G) : Equation2293 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq24 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.1 in 12
  have eq33 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq32 eq24 -- backward demodulation 24,32
  subsumption eq33 eq12


@[equational_result]
theorem Equation3108_implies_Equation4635 (G : Type*) [Magma G] (h : Equation3108 G) : Equation4635 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : ((sK1 ◇ sK0) ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq24 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq33 : sK0 ≠ sK0 := superpose eq24 eq14 -- superposition 14,24, 24 into 14, unify on (0).2 in 24 and (0).2 in 14
  subsumption eq33 rfl


@[equational_result]
theorem Equation3108_implies_Equation4445 (G : Type*) [Magma G] (h : Equation3108 G) : Equation4445 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK1 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.1 in 12
  have eq47 : (sK1 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq32 eq15 -- superposition 15,32, 32 into 15, unify on (0).2 in 32 and (0).2 in 15
  subsumption eq47 rfl


@[equational_result]
theorem Equation3108_implies_Equation4396 (G : Type*) [Magma G] (h : Equation3108 G) : Equation4396 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq39 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq39 rfl


@[equational_result]
theorem Equation3108_implies_Equation4291 (G : Type*) [Magma G] (h : Equation3108 G) : Equation4291 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq24 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.1 in 12
  have eq47 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq24 -- superposition 24,32, 32 into 24, unify on (0).2 in 32 and (0).2 in 24
  subsumption eq47 rfl


@[equational_result]
theorem Equation3108_implies_Equation3880 (G : Type*) [Magma G] (h : Equation3108 G) : Equation3880 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.1 in 12
  have eq33 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq32 eq15 -- backward demodulation 15,32
  subsumption eq33 eq12


@[equational_result]
theorem Equation3108_implies_Equation3712 (G : Type*) [Magma G] (h : Equation3108 G) : Equation3712 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq39 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq39 rfl


@[equational_result]
theorem Equation3108_implies_Equation3664 (G : Type*) [Magma G] (h : Equation3108 G) : Equation3664 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq12


@[equational_result]
theorem Equation3108_implies_Equation3546 (G : Type*) [Magma G] (h : Equation3108 G) : Equation3546 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.1 in 12
  have eq47 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq15 -- superposition 15,32, 32 into 15, unify on (0).2 in 32 and (0).2 in 15
  subsumption eq47 rfl


@[equational_result]
theorem Equation3108_implies_Equation3509 (G : Type*) [Magma G] (h : Equation3108 G) : Equation3509 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq39 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq39 rfl


@[equational_result]
theorem Equation3108_implies_Equation3353 (G : Type*) [Magma G] (h : Equation3108 G) : Equation3353 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.1 in 12
  have eq32 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq31 eq10 -- backward demodulation 10,31
  subsumption eq32 eq31


@[equational_result]
theorem Equation3108_implies_Equation3346 (G : Type*) [Magma G] (h : Equation3108 G) : Equation3346 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.1 in 12
  have eq47 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq15 -- superposition 15,32, 32 into 15, unify on (0).2 in 32 and (0).2 in 15
  subsumption eq47 rfl


@[equational_result]
theorem Equation3108_implies_Equation3343 (G : Type*) [Magma G] (h : Equation3108 G) : Equation3343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq24 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.1 in 12
  have eq47 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq24 -- superposition 24,32, 32 into 24, unify on (0).2 in 32 and (0).2 in 24
  subsumption eq47 rfl


@[equational_result]
theorem Equation3108_implies_Equation2662 (G : Type*) [Magma G] (h : Equation3108 G) : Equation2662 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq12


@[equational_result]
theorem Equation3108_implies_Equation2496 (G : Type*) [Magma G] (h : Equation3108 G) : Equation2496 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.1 in 12
  have eq33 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq32 eq15 -- backward demodulation 15,32
  subsumption eq33 eq12


@[equational_result]
theorem Equation3108_implies_Equation2303 (G : Type*) [Magma G] (h : Equation3108 G) : Equation2303 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).1.1 in 12
  have eq33 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq32 eq15 -- backward demodulation 15,32
  subsumption eq33 eq12


@[equational_result]
theorem Equation3108_implies_Equation1857 (G : Type*) [Magma G] (h : Equation3108 G) : Equation1857 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq12


@[equational_result]
theorem Equation3108_implies_Equation1684 (G : Type*) [Magma G] (h : Equation3108 G) : Equation1684 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq23 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq32 : sK0 ≠ sK0 := superpose eq23 eq14 -- superposition 14,23, 23 into 14, unify on (0).2 in 23 and (0).2 in 14
  subsumption eq32 rfl


@[equational_result]
theorem Equation3108_implies_Equation1441 (G : Type*) [Magma G] (h : Equation3108 G) : Equation1441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq15 -- forward demodulation 15,13
  subsumption eq16 eq12


@[equational_result]
theorem Equation3108_implies_Equation822 (G : Type*) [Magma G] (h : Equation3108 G) : Equation822 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq13


@[equational_result]
theorem Equation3108_implies_Equation1225 (G : Type*) [Magma G] (h : Equation3108 G) : Equation1225 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X1 X3 : G) : (((X1 ◇ X1) ◇ X3) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation3108_implies_Equation616 (G : Type*) [Magma G] (h : Equation3108 G) : Equation616 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq14 -- backward demodulation 14,13
  subsumption eq16 eq13


@[equational_result]
theorem Equation3108_implies_Equation4642 (G : Type*) [Magma G] (h : Equation3108 G) : Equation4642 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK2 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 : sK0 ≠ ((sK2 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq24 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq33 : sK0 ≠ sK0 := superpose eq24 eq14 -- superposition 14,24, 24 into 14, unify on (0).2 in 24 and (0).2 in 14
  subsumption eq33 rfl


@[equational_result]
theorem Equation3108_implies_Equation1867 (G : Type*) [Magma G] (h : Equation3108 G) : Equation1867 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq12


@[equational_result]
theorem Equation3108_implies_Equation333 (G : Type*) [Magma G] (h : Equation3108 G) : Equation333 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.1 in 12
  have eq46 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq31 eq10 -- superposition 10,31, 31 into 10, unify on (0).2 in 31 and (0).2 in 10
  subsumption eq46 rfl


@[equational_result]
theorem Equation3108_implies_Equation1687 (G : Type*) [Magma G] (h : Equation3108 G) : Equation1687 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq23 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq32 : sK0 ≠ sK0 := superpose eq23 eq14 -- superposition 14,23, 23 into 14, unify on (0).2 in 23 and (0).2 in 14
  subsumption eq32 rfl


@[equational_result]
theorem Equation3108_implies_Equation2337 (G : Type*) [Magma G] (h : Equation3108 G) : Equation2337 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq24 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq25 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq19 eq24 -- forward demodulation 24,19
  have eq33 : sK0 ≠ sK0 := superpose eq22 eq25 -- superposition 25,22, 22 into 25, unify on (0).2 in 22 and (0).2 in 25
  subsumption eq33 rfl


@[equational_result]
theorem Equation3108_implies_Equation2513 (G : Type*) [Magma G] (h : Equation3108 G) : Equation2513 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK2) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq23 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq32 : sK0 ≠ sK0 := superpose eq23 eq14 -- superposition 14,23, 23 into 14, unify on (0).2 in 23 and (0).2 in 14
  subsumption eq32 rfl


@[equational_result]
theorem Equation3077_implies_Equation3266 (G : Type*) [Magma G] (h : Equation3077 G) : Equation3266 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation3077_implies_Equation3459 (G : Type*) [Magma G] (h : Equation3077 G) : Equation3459 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation3077_implies_Equation3069 (G : Type*) [Magma G] (h : Equation3077 G) : Equation3069 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq37 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.1 in 9
  have eq41 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ X0) ◇ sK1) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).2.1 in 15
  subsumption eq41 eq37


@[equational_result]
theorem Equation3077_implies_Equation3055 (G : Type*) [Magma G] (h : Equation3077 G) : Equation3055 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ X2) := superpose eq13 eq12 -- backward demodulation 12,13
  have eq42 (X0 : G) : sK0 ≠ ((((sK0 ◇ X0) ◇ X0) ◇ sK0) ◇ sK0) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.1.1 in 10
  subsumption eq42 eq9


@[equational_result]
theorem Equation3077_implies_Equation3080 (G : Type*) [Magma G] (h : Equation3077 G) : Equation3080 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ X2) := superpose eq13 eq12 -- backward demodulation 12,13
  have eq15 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq34 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.1 in 9
  have eq88 (X0 : G) : sK0 ≠ ((((sK0 ◇ X0) ◇ X0) ◇ sK1) ◇ sK2) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2.1.1 in 15
  subsumption eq88 eq34


@[equational_result]
theorem Equation3077_implies_Equation3529 (G : Type*) [Magma G] (h : Equation3077 G) : Equation3529 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation3077_implies_Equation3323 (G : Type*) [Magma G] (h : Equation3077 G) : Equation3323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation3077_implies_Equation3053 (G : Type*) [Magma G] (h : Equation3077 G) : Equation3053 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq63 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.1 in 9
  have eq75 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ X0) ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2.1 in 10
  subsumption eq75 eq63


@[equational_result]
theorem Equation3077_implies_Equation4360 (G : Type*) [Magma G] (h : Equation3077 G) : Equation4360 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ sK2)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation3077_implies_Equation3513 (G : Type*) [Magma G] (h : Equation3077 G) : Equation3513 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation1440_implies_Equation1856 (G : Type*) [Magma G] (h : Equation1440 G) : Equation1856 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : ((X4 ◇ X4) ◇ (X5 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X4 : G) : ((X4 ◇ X4) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq19 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK2 ◇ sK3)) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq19 eq12


@[equational_result]
theorem Equation2084_implies_Equation267 (G : Type*) [Magma G] (h : Equation2084 G) : Equation267 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X0 ◇ (X4 ◇ (X3 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X2 X3 X4 X5 : G) : (((X4 ◇ X5) ◇ (X3 ◇ X2)) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 X4 X5 : G) : (X4 ◇ X5) = (X4 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq38 (X0 X4 X5 X6 : G) : (((X4 ◇ X5) ◇ X0) ◇ X6) = X4 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq67 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK2) ◇ sK1) := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2.1.1 in 10
  subsumption eq67 eq38


@[equational_result]
theorem Equation1152_implies_Equation2534 (G : Type*) [Magma G] (h : Equation1152 G) : Equation2534 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ ((X3 ◇ X2) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq18 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ (((X3 ◇ X1) ◇ X3) ◇ X5)) ◇ X4) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))) = X5 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq23 (X1 X3 X4 X5 : G) : (((X4 ◇ (((X3 ◇ X1) ◇ X3) ◇ X5)) ◇ X4) ◇ X1) = X5 := superpose eq9 eq18 -- forward demodulation 18,9
  have eq28 (X1 X2 X3 X4 : G) : ((X3 ◇ X1) ◇ X3) = (((X4 ◇ X2) ◇ X4) ◇ (X1 ◇ X2)) := superpose eq11 eq23 -- superposition 23,11, 11 into 23, unify on (0).2 in 11 and (0).1.1.1.2 in 23
  have eq62 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X4) = (((X5 ◇ (X2 ◇ X1)) ◇ X5) ◇ ((X3 ◇ X2) ◇ X3)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq101 (X0 X1 X4 : G) : ((X4 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X4) = X1 := superpose eq11 eq62 -- forward demodulation 62,11
  have eq271 : sK0 ≠ sK0 := superpose eq101 eq10 -- superposition 10,101, 101 into 10, unify on (0).2 in 101 and (0).2 in 10
  subsumption eq271 rfl


@[equational_result]
theorem Equation1152_implies_Equation4647 (G : Type*) [Magma G] (h : Equation1152 G) : Equation4647 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK2 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ ((X3 ◇ X2) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq18 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ (((X3 ◇ X1) ◇ X3) ◇ X5)) ◇ X4) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))) = X5 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq23 (X1 X3 X4 X5 : G) : (((X4 ◇ (((X3 ◇ X1) ◇ X3) ◇ X5)) ◇ X4) ◇ X1) = X5 := superpose eq9 eq18 -- forward demodulation 18,9
  have eq28 (X1 X2 X3 X4 : G) : ((X3 ◇ X1) ◇ X3) = (((X4 ◇ X2) ◇ X4) ◇ (X1 ◇ X2)) := superpose eq11 eq23 -- superposition 23,11, 11 into 23, unify on (0).2 in 11 and (0).1.1.1.2 in 23
  have eq60 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ X3) = (((X4 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X4) ◇ X2) := superpose eq9 eq28 -- superposition 28,9, 9 into 28, unify on (0).2 in 9 and (0).2.2 in 28
  have eq62 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X4) = (((X5 ◇ (X2 ◇ X1)) ◇ X5) ◇ ((X3 ◇ X2) ◇ X3)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq101 (X0 X1 X4 : G) : ((X4 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X4) = X1 := superpose eq11 eq62 -- forward demodulation 62,11
  have eq103 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq101 eq60 -- backward demodulation 60,101
  have eq433 (X0 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ ((X0 ◇ sK1) ◇ X0) := superpose eq103 eq10 -- superposition 10,103, 103 into 10, unify on (0).2 in 103 and (0).2 in 10
  subsumption eq433 eq103


@[equational_result]
theorem Equation1152_implies_Equation2576 (G : Type*) [Magma G] (h : Equation1152 G) : Equation2576 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK0) ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ ((X3 ◇ X2) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq18 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ (((X3 ◇ X1) ◇ X3) ◇ X5)) ◇ X4) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))) = X5 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq23 (X1 X3 X4 X5 : G) : (((X4 ◇ (((X3 ◇ X1) ◇ X3) ◇ X5)) ◇ X4) ◇ X1) = X5 := superpose eq9 eq18 -- forward demodulation 18,9
  have eq28 (X1 X2 X3 X4 : G) : ((X3 ◇ X1) ◇ X3) = (((X4 ◇ X2) ◇ X4) ◇ (X1 ◇ X2)) := superpose eq11 eq23 -- superposition 23,11, 11 into 23, unify on (0).2 in 11 and (0).1.1.1.2 in 23
  have eq62 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X4) = (((X5 ◇ (X2 ◇ X1)) ◇ X5) ◇ ((X3 ◇ X2) ◇ X3)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq101 (X0 X1 X4 : G) : ((X4 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X4) = X1 := superpose eq11 eq62 -- forward demodulation 62,11
  have eq271 : sK0 ≠ sK0 := superpose eq101 eq10 -- superposition 10,101, 101 into 10, unify on (0).2 in 101 and (0).2 in 10
  subsumption eq271 rfl


@[equational_result]
theorem Equation796_implies_Equation938 (G : Type*) [Magma G] (h : Equation796 G) : Equation938 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X2 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X3 X4 X5 : G) : (X5 ◇ X4) = (X3 ◇ X4) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq24 (X1 X2 X3 X4 : G) : (X1 ◇ (X4 ◇ (X3 ◇ X2))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq89 (X0 : G) : sK0 ≠ (X0 ◇ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK0))) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq89 eq24


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
theorem Equation483_implies_Equation4320 (G : Type*) [Magma G] (h : Equation483 G) : Equation4320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : (sK1 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq22 (X0 : G) : (sK1 ◇ (X0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).1.2 in 13
  subsumption eq22 eq15


@[equational_result]
theorem Equation483_implies_Equation3905 (G : Type*) [Magma G] (h : Equation483 G) : Equation3905 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation387_implies_Equation332 (G : Type*) [Magma G] (h : Equation387 G) : Equation332 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X1) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq16 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq19 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq20 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = (X1 ◇ X0) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq27 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq9 eq20 -- superposition 20,9, 9 into 20, unify on (0).2 in 9 and (0).1 in 20
  have eq49 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq27 eq19 -- superposition 19,27, 27 into 19, unify on (0).2 in 27 and (0).2 in 19
  subsumption eq49 rfl


@[equational_result]
theorem Equation387_implies_Equation3758 (G : Type*) [Magma G] (h : Equation387 G) : Equation3758 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq20 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 eq9


@[equational_result]
theorem Equation3940_implies_Equation4383 (G : Type*) [Magma G] (h : Equation3940 G) : Equation4383 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) = ((X0 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X3 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq16 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) = ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ (X4 ◇ X1)) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.1 in 9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2 in 21
  have eq109 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X3))) = ((X5 ◇ (X0 ◇ X4)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2.1.2 in 9
  have eq134 (X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X3))) = (X5 ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq17 eq109 -- forward demodulation 109,17
  have eq143 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.1 in 58
  have eq192 (X1 X2 X3 X4 X5 : G) : (X5 ◇ (X1 ◇ (X4 ◇ X2))) = (X5 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X3)))) := superpose eq143 eq134 -- backward demodulation 134,143
  have eq261 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ ((X0 ◇ X2) ◇ X4)) ◇ X5) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.1.2.1 in 16
  have eq269 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ ((X0 ◇ X3) ◇ X1)) ◇ X5) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).1.1.2 in 16
  have eq279 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq12 eq16 -- superposition 16,12, 12 into 16, unify on (0).2 in 12 and (0).1 in 16
  have eq280 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1 in 16
  have eq303 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) := superpose eq143 eq261 -- forward demodulation 261,143
  have eq304 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X5 ◇ X1)))) := superpose eq143 eq303 -- forward demodulation 303,143
  have eq305 (X0 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ (X0 ◇ (X5 ◇ X2))) := superpose eq192 eq304 -- forward demodulation 304,192
  have eq332 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ ((X0 ◇ X3) ◇ X5)) := superpose eq143 eq269 -- forward demodulation 269,143
  have eq333 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq305 eq332 -- forward demodulation 332,305
  have eq502 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = ((X4 ◇ (X6 ◇ X5)) ◇ (X6 ◇ (X0 ◇ X3))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2.2.2 in 17
  have eq519 (X0 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X3 ◇ (X2 ◇ X2))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2 in 17
  have eq520 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X3))) := superpose eq21 eq17 -- superposition 17,21, 21 into 17, unify on (0).2 in 21 and (0).2 in 17
  have eq572 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq17 eq502 -- forward demodulation 502,17
  have eq573 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X3))) = (X4 ◇ ((X0 ◇ X3) ◇ (X5 ◇ (X1 ◇ X1)))) := superpose eq333 eq572 -- forward demodulation 572,333
  have eq574 (X0 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ X3) ◇ X5)) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq279 eq573 -- forward demodulation 573,279
  have eq578 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq574 eq280 -- backward demodulation 280,574
  have eq585 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X2) := superpose eq574 eq12 -- backward demodulation 12,574
  have eq754 (X0 X1 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ X1)) := superpose eq519 eq578 -- backward demodulation 578,519
  have eq755 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X3)))) := superpose eq574 eq520 -- forward demodulation 520,574
  have eq756 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ X2)) := superpose eq519 eq755 -- forward demodulation 755,519
  have eq810 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = (X0 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq17 eq519 -- superposition 519,17, 17 into 519, unify on (0).2 in 17 and (0).2 in 519
  have eq851 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq9 eq810 -- forward demodulation 810,9
  have eq902 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq519 eq585 -- superposition 585,519, 519 into 585, unify on (0).2 in 519 and (0).2.1.2 in 585
  have eq966 (X0 X1 X3 : G) : ((X3 ◇ X1) ◇ X0) = (X3 ◇ (X0 ◇ X1)) := superpose eq754 eq902 -- forward demodulation 902,754
  have eq967 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq966 eq21 -- backward demodulation 21,966
  have eq999 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X3)) = ((X0 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X2) := superpose eq966 eq585 -- backward demodulation 585,966
  have eq1458 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X1 ◇ X2)) := superpose eq9 eq999 -- superposition 999,9, 9 into 999, unify on (0).2 in 9 and (0).2 in 999
  have eq1690 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X3))) := superpose eq17 eq967 -- superposition 967,17, 17 into 967, unify on (0).2 in 17 and (0).1 in 967
  have eq1740 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3)))) := superpose eq1458 eq1690 -- forward demodulation 1690,1458
  have eq1741 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose eq851 eq1740 -- forward demodulation 1740,851
  have eq1836 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq756 eq10 -- superposition 10,756, 756 into 10, unify on (0).2 in 756 and (0).2 in 10
  subsumption eq1836 eq1741


@[equational_result]
theorem Equation3940_implies_Equation4073 (G : Type*) [Magma G] (h : Equation3940 G) : Equation4073 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) = ((X0 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X3 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq16 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) = ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ (X4 ◇ X1)) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.1 in 9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2 in 21
  have eq109 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X3))) = ((X5 ◇ (X0 ◇ X4)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2.1.2 in 9
  have eq134 (X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X3))) = (X5 ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq17 eq109 -- forward demodulation 109,17
  have eq143 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.1 in 58
  have eq161 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X2) ◇ X1) := superpose eq58 eq9 -- superposition 9,58, 58 into 9, unify on (0).2 in 58 and (0).2.1 in 9
  have eq192 (X1 X2 X3 X4 X5 : G) : (X5 ◇ (X1 ◇ (X4 ◇ X2))) = (X5 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X3)))) := superpose eq143 eq134 -- backward demodulation 134,143
  have eq261 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ ((X0 ◇ X2) ◇ X4)) ◇ X5) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.1.2.1 in 16
  have eq269 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ ((X0 ◇ X3) ◇ X1)) ◇ X5) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).1.1.2 in 16
  have eq279 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq12 eq16 -- superposition 16,12, 12 into 16, unify on (0).2 in 12 and (0).1 in 16
  have eq280 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1 in 16
  have eq303 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) := superpose eq143 eq261 -- forward demodulation 261,143
  have eq304 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X5 ◇ X1)))) := superpose eq143 eq303 -- forward demodulation 303,143
  have eq305 (X0 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ (X0 ◇ (X5 ◇ X2))) := superpose eq192 eq304 -- forward demodulation 304,192
  have eq332 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ ((X0 ◇ X3) ◇ X5)) := superpose eq143 eq269 -- forward demodulation 269,143
  have eq333 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq305 eq332 -- forward demodulation 332,305
  have eq426 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := superpose eq161 eq10 -- superposition 10,161, 161 into 10, unify on (0).2 in 161 and (0).2 in 10
  have eq474 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq161 eq426 -- forward demodulation 426,161
  have eq506 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = ((X4 ◇ (X6 ◇ X5)) ◇ (X6 ◇ (X0 ◇ X3))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2.2.2 in 17
  have eq523 (X0 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X3 ◇ (X2 ◇ X2))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2 in 17
  have eq576 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq17 eq506 -- forward demodulation 506,17
  have eq577 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X3))) = (X4 ◇ ((X0 ◇ X3) ◇ (X5 ◇ (X1 ◇ X1)))) := superpose eq333 eq576 -- forward demodulation 576,333
  have eq578 (X0 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ X3) ◇ X5)) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq279 eq577 -- forward demodulation 577,279
  have eq582 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq578 eq280 -- backward demodulation 280,578
  have eq589 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X2) := superpose eq578 eq12 -- backward demodulation 12,578
  have eq758 (X0 X1 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ X1)) := superpose eq523 eq582 -- backward demodulation 582,523
  have eq906 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq523 eq589 -- superposition 589,523, 523 into 589, unify on (0).2 in 523 and (0).2.1.2 in 589
  have eq970 (X0 X1 X3 : G) : ((X3 ◇ X1) ◇ X0) = (X3 ◇ (X0 ◇ X1)) := superpose eq758 eq906 -- forward demodulation 906,758
  have eq1120 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := superpose eq970 eq474 -- backward demodulation 474,970
  subsumption eq1120 eq9


@[equational_result]
theorem Equation3940_implies_Equation4127 (G : Type*) [Magma G] (h : Equation3940 G) : Equation4127 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) = ((X0 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X3 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq16 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) = ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ (X4 ◇ X1)) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.1 in 9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2 in 21
  have eq82 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) = ((X0 ◇ X3) ◇ ((X1 ◇ (X5 ◇ X2)) ◇ (X4 ◇ X5))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq117 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) = ((X0 ◇ X3) ◇ ((X1 ◇ (X5 ◇ X2)) ◇ (X4 ◇ X5))) := superpose eq16 eq82 -- forward demodulation 82,16
  have eq143 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.1 in 58
  have eq164 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X2) ◇ X1) := superpose eq58 eq9 -- superposition 9,58, 58 into 9, unify on (0).2 in 58 and (0).2.1 in 9
  have eq194 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) = ((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ (X5 ◇ (X4 ◇ X5)))) := superpose eq143 eq117 -- backward demodulation 117,143
  have eq251 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := superpose eq164 eq10 -- backward demodulation 10,164
  have eq338 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ ((X0 ◇ X2) ◇ X4)) ◇ X5) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.1.2.1 in 16
  have eq348 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ ((X0 ◇ X3) ◇ X1)) ◇ X5) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).1.1.2 in 16
  have eq362 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq12 eq16 -- superposition 16,12, 12 into 16, unify on (0).2 in 12 and (0).1 in 16
  have eq363 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1 in 16
  have eq392 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) := superpose eq143 eq338 -- forward demodulation 338,143
  have eq393 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X5 ◇ X1)))) := superpose eq143 eq392 -- forward demodulation 392,143
  have eq394 (X0 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ (X0 ◇ (X5 ◇ X2))) := superpose eq194 eq393 -- forward demodulation 393,194
  have eq425 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ ((X0 ◇ X3) ◇ X5)) := superpose eq143 eq348 -- forward demodulation 348,143
  have eq426 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq394 eq425 -- forward demodulation 425,394
  have eq505 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = ((X4 ◇ (X6 ◇ X5)) ◇ (X6 ◇ (X0 ◇ X3))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2.2.2 in 17
  have eq522 (X0 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X3 ◇ (X2 ◇ X2))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2 in 17
  have eq575 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq17 eq505 -- forward demodulation 505,17
  have eq576 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X3))) = (X4 ◇ ((X0 ◇ X3) ◇ (X5 ◇ (X1 ◇ X1)))) := superpose eq426 eq575 -- forward demodulation 575,426
  have eq577 (X0 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ X3) ◇ X5)) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq362 eq576 -- forward demodulation 576,362
  have eq581 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq577 eq363 -- backward demodulation 363,577
  have eq588 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X2) := superpose eq577 eq12 -- backward demodulation 12,577
  have eq755 (X0 X1 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ X1)) := superpose eq522 eq581 -- backward demodulation 581,522
  have eq904 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq522 eq588 -- superposition 588,522, 522 into 588, unify on (0).2 in 522 and (0).2.1.2 in 588
  have eq968 (X0 X1 X3 : G) : ((X3 ◇ X1) ◇ X0) = (X3 ◇ (X0 ◇ X1)) := superpose eq755 eq904 -- forward demodulation 904,755
  have eq1001 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X3)) = ((X0 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X2) := superpose eq968 eq588 -- backward demodulation 588,968
  have eq1119 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq968 eq251 -- backward demodulation 251,968
  have eq1416 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X1 ◇ X2)) := superpose eq9 eq1001 -- superposition 1001,9, 9 into 1001, unify on (0).2 in 9 and (0).2 in 1001
  have eq1454 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq1416 eq1119 -- backward demodulation 1119,1416
  subsumption eq1454 eq9


@[equational_result]
theorem Equation3940_implies_Equation4118 (G : Type*) [Magma G] (h : Equation3940 G) : Equation4118 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) = ((X0 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X3 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq16 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) = ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ (X4 ◇ X1)) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.1 in 9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2 in 21
  have eq109 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X3))) = ((X5 ◇ (X0 ◇ X4)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2.1.2 in 9
  have eq134 (X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X3))) = (X5 ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq17 eq109 -- forward demodulation 109,17
  have eq143 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.1 in 58
  have eq161 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X2) ◇ X1) := superpose eq58 eq9 -- superposition 9,58, 58 into 9, unify on (0).2 in 58 and (0).2.1 in 9
  have eq192 (X1 X2 X3 X4 X5 : G) : (X5 ◇ (X1 ◇ (X4 ◇ X2))) = (X5 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X3)))) := superpose eq143 eq134 -- backward demodulation 134,143
  have eq261 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ ((X0 ◇ X2) ◇ X4)) ◇ X5) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.1.2.1 in 16
  have eq269 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ ((X0 ◇ X3) ◇ X1)) ◇ X5) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).1.1.2 in 16
  have eq279 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq12 eq16 -- superposition 16,12, 12 into 16, unify on (0).2 in 12 and (0).1 in 16
  have eq280 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1 in 16
  have eq303 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) := superpose eq143 eq261 -- forward demodulation 261,143
  have eq304 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X5 ◇ X1)))) := superpose eq143 eq303 -- forward demodulation 303,143
  have eq305 (X0 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ (X0 ◇ (X5 ◇ X2))) := superpose eq192 eq304 -- forward demodulation 304,192
  have eq332 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ ((X0 ◇ X3) ◇ X5)) := superpose eq143 eq269 -- forward demodulation 269,143
  have eq333 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq305 eq332 -- forward demodulation 332,305
  have eq502 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = ((X4 ◇ (X6 ◇ X5)) ◇ (X6 ◇ (X0 ◇ X3))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2.2.2 in 17
  have eq519 (X0 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X3 ◇ (X2 ◇ X2))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2 in 17
  have eq572 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq17 eq502 -- forward demodulation 502,17
  have eq573 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X3))) = (X4 ◇ ((X0 ◇ X3) ◇ (X5 ◇ (X1 ◇ X1)))) := superpose eq333 eq572 -- forward demodulation 572,333
  have eq574 (X0 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ X3) ◇ X5)) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq279 eq573 -- forward demodulation 573,279
  have eq578 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq574 eq280 -- backward demodulation 280,574
  have eq585 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X2) := superpose eq574 eq12 -- backward demodulation 12,574
  have eq754 (X0 X1 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ X1)) := superpose eq519 eq578 -- backward demodulation 578,519
  have eq810 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = (X0 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq17 eq519 -- superposition 519,17, 17 into 519, unify on (0).2 in 17 and (0).2 in 519
  have eq851 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq9 eq810 -- forward demodulation 810,9
  have eq891 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X4) = ((X3 ◇ (X4 ◇ ((X0 ◇ X2) ◇ X1))) ◇ X2) := superpose eq161 eq585 -- superposition 585,161, 161 into 585, unify on (0).2 in 161 and (0).2.1.2.2 in 585
  have eq902 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq519 eq585 -- superposition 585,519, 519 into 585, unify on (0).2 in 519 and (0).2.1.2 in 585
  have eq932 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X2) ◇ X1) ◇ X3) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X4) := superpose eq585 eq9 -- superposition 9,585, 585 into 9, unify on (0).2 in 585 and (0).2.1 in 9
  have eq951 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X4) = ((X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X2) := superpose eq574 eq891 -- forward demodulation 891,574
  have eq952 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X1) ◇ (X0 ◇ X4)) = ((X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X2) := superpose eq143 eq951 -- forward demodulation 951,143
  have eq966 (X0 X1 X3 : G) : ((X3 ◇ X1) ◇ X0) = (X3 ◇ (X0 ◇ X1)) := superpose eq754 eq902 -- forward demodulation 902,754
  have eq1058 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X2) = (X3 ◇ ((X0 ◇ X4) ◇ X1)) := superpose eq966 eq952 -- backward demodulation 952,966
  have eq1115 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := superpose eq966 eq10 -- backward demodulation 10,966
  have eq1206 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ X4))) := superpose eq966 eq1058 -- forward demodulation 1058,966
  have eq1374 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X1) ◇ X3) = (X0 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq1206 eq932 -- forward demodulation 932,1206
  have eq1375 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq966 eq1374 -- forward demodulation 1374,966
  have eq1838 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := superpose eq1375 eq1115 -- superposition 1115,1375, 1375 into 1115, unify on (0).2 in 1375 and (0).2 in 1115
  subsumption eq1838 eq851


@[equational_result]
theorem Equation3940_implies_Equation3665 (G : Type*) [Magma G] (h : Equation3940 G) : Equation3665 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) = ((X0 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X3 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq16 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) = ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ (X4 ◇ X1)) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.1 in 9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2 in 21
  have eq82 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) = ((X0 ◇ X3) ◇ ((X1 ◇ (X5 ◇ X2)) ◇ (X4 ◇ X5))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq117 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) = ((X0 ◇ X3) ◇ ((X1 ◇ (X5 ◇ X2)) ◇ (X4 ◇ X5))) := superpose eq16 eq82 -- forward demodulation 82,16
  have eq143 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.1 in 58
  have eq194 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) = ((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ (X5 ◇ (X4 ◇ X5)))) := superpose eq143 eq117 -- backward demodulation 117,143
  have eq261 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ ((X0 ◇ X2) ◇ X4)) ◇ X5) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.1.2.1 in 16
  have eq269 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ ((X0 ◇ X3) ◇ X1)) ◇ X5) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).1.1.2 in 16
  have eq279 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq12 eq16 -- superposition 16,12, 12 into 16, unify on (0).2 in 12 and (0).1 in 16
  have eq280 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1 in 16
  have eq303 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) := superpose eq143 eq261 -- forward demodulation 261,143
  have eq304 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X5 ◇ X1)))) := superpose eq143 eq303 -- forward demodulation 303,143
  have eq305 (X0 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ (X0 ◇ (X5 ◇ X2))) := superpose eq194 eq304 -- forward demodulation 304,194
  have eq332 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ ((X0 ◇ X3) ◇ X5)) := superpose eq143 eq269 -- forward demodulation 269,143
  have eq333 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq305 eq332 -- forward demodulation 332,305
  have eq502 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = ((X4 ◇ (X6 ◇ X5)) ◇ (X6 ◇ (X0 ◇ X3))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2.2.2 in 17
  have eq519 (X0 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X3 ◇ (X2 ◇ X2))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2 in 17
  have eq572 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq17 eq502 -- forward demodulation 502,17
  have eq573 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X3))) = (X4 ◇ ((X0 ◇ X3) ◇ (X5 ◇ (X1 ◇ X1)))) := superpose eq333 eq572 -- forward demodulation 572,333
  have eq574 (X0 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ X3) ◇ X5)) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq279 eq573 -- forward demodulation 573,279
  have eq578 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq574 eq280 -- backward demodulation 280,574
  have eq585 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X2) := superpose eq574 eq12 -- backward demodulation 12,574
  have eq754 (X0 X1 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ X1)) := superpose eq519 eq578 -- backward demodulation 578,519
  have eq903 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq519 eq585 -- superposition 585,519, 519 into 585, unify on (0).2 in 519 and (0).2.1.2 in 585
  have eq967 (X0 X1 X3 : G) : ((X3 ◇ X1) ◇ X0) = (X3 ◇ (X0 ◇ X1)) := superpose eq754 eq903 -- forward demodulation 903,754
  have eq3947 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := superpose eq967 eq10 -- superposition 10,967, 967 into 10, unify on (0).2 in 967 and (0).2 in 10
  have eq4038 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := superpose eq967 eq3947 -- forward demodulation 3947,967
  subsumption eq4038 eq519


@[equational_result]
theorem Equation3940_implies_Equation4469 (G : Type*) [Magma G] (h : Equation3940 G) : Equation4469 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) = ((X0 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X3 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq16 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) = ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ (X4 ◇ X1)) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.1 in 9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2 in 21
  have eq109 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X3))) = ((X5 ◇ (X0 ◇ X4)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2.1.2 in 9
  have eq134 (X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X3))) = (X5 ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq17 eq109 -- forward demodulation 109,17
  have eq143 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.1 in 58
  have eq192 (X1 X2 X3 X4 X5 : G) : (X5 ◇ (X1 ◇ (X4 ◇ X2))) = (X5 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X3)))) := superpose eq143 eq134 -- backward demodulation 134,143
  have eq261 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ ((X0 ◇ X2) ◇ X4)) ◇ X5) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.1.2.1 in 16
  have eq269 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ ((X0 ◇ X3) ◇ X1)) ◇ X5) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).1.1.2 in 16
  have eq279 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq12 eq16 -- superposition 16,12, 12 into 16, unify on (0).2 in 12 and (0).1 in 16
  have eq280 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1 in 16
  have eq303 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) := superpose eq143 eq261 -- forward demodulation 261,143
  have eq304 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X5 ◇ X1)))) := superpose eq143 eq303 -- forward demodulation 303,143
  have eq305 (X0 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ (X0 ◇ (X5 ◇ X2))) := superpose eq192 eq304 -- forward demodulation 304,192
  have eq332 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ ((X0 ◇ X3) ◇ X5)) := superpose eq143 eq269 -- forward demodulation 269,143
  have eq333 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq305 eq332 -- forward demodulation 332,305
  have eq502 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = ((X4 ◇ (X6 ◇ X5)) ◇ (X6 ◇ (X0 ◇ X3))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2.2.2 in 17
  have eq519 (X0 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X3 ◇ (X2 ◇ X2))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2 in 17
  have eq572 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq17 eq502 -- forward demodulation 502,17
  have eq573 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X3))) = (X4 ◇ ((X0 ◇ X3) ◇ (X5 ◇ (X1 ◇ X1)))) := superpose eq333 eq572 -- forward demodulation 572,333
  have eq574 (X0 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ X3) ◇ X5)) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq279 eq573 -- forward demodulation 573,279
  have eq578 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq574 eq280 -- backward demodulation 280,574
  have eq585 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X2) := superpose eq574 eq12 -- backward demodulation 12,574
  have eq754 (X0 X1 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ X1)) := superpose eq519 eq578 -- backward demodulation 578,519
  have eq810 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = (X0 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq17 eq519 -- superposition 519,17, 17 into 519, unify on (0).2 in 17 and (0).2 in 519
  have eq851 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq9 eq810 -- forward demodulation 810,9
  have eq902 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq519 eq585 -- superposition 585,519, 519 into 585, unify on (0).2 in 519 and (0).2.1.2 in 585
  have eq966 (X0 X1 X3 : G) : ((X3 ◇ X1) ◇ X0) = (X3 ◇ (X0 ◇ X1)) := superpose eq754 eq902 -- forward demodulation 902,754
  have eq967 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq966 eq21 -- backward demodulation 21,966
  have eq999 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X3)) = ((X0 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X2) := superpose eq966 eq585 -- backward demodulation 585,966
  have eq1115 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq966 eq10 -- backward demodulation 10,966
  have eq1412 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X1 ◇ X2)) := superpose eq9 eq999 -- superposition 999,9, 9 into 999, unify on (0).2 in 9 and (0).2 in 999
  have eq1626 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X3))) := superpose eq17 eq967 -- superposition 967,17, 17 into 967, unify on (0).2 in 17 and (0).1 in 967
  have eq1674 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3)))) := superpose eq1412 eq1626 -- forward demodulation 1626,1412
  have eq1675 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose eq851 eq1674 -- forward demodulation 1674,851
  have eq2672 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq1675 eq1115 -- superposition 1115,1675, 1675 into 1115, unify on (0).2 in 1675 and (0).1 in 1115
  subsumption eq2672 eq1675


@[equational_result]
theorem Equation3940_implies_Equation3714 (G : Type*) [Magma G] (h : Equation3940 G) : Equation3714 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) = ((X0 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X3 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq16 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) = ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ (X4 ◇ X1)) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.1 in 9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2 in 21
  have eq109 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X3))) = ((X5 ◇ (X0 ◇ X4)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2.1.2 in 9
  have eq134 (X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X3))) = (X5 ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq17 eq109 -- forward demodulation 109,17
  have eq143 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.1 in 58
  have eq192 (X1 X2 X3 X4 X5 : G) : (X5 ◇ (X1 ◇ (X4 ◇ X2))) = (X5 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X3)))) := superpose eq143 eq134 -- backward demodulation 134,143
  have eq261 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ ((X0 ◇ X2) ◇ X4)) ◇ X5) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.1.2.1 in 16
  have eq269 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ ((X0 ◇ X3) ◇ X1)) ◇ X5) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).1.1.2 in 16
  have eq279 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq12 eq16 -- superposition 16,12, 12 into 16, unify on (0).2 in 12 and (0).1 in 16
  have eq280 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1 in 16
  have eq303 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) := superpose eq143 eq261 -- forward demodulation 261,143
  have eq304 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X5 ◇ X1)))) := superpose eq143 eq303 -- forward demodulation 303,143
  have eq305 (X0 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ (X0 ◇ (X5 ◇ X2))) := superpose eq192 eq304 -- forward demodulation 304,192
  have eq332 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ ((X0 ◇ X3) ◇ X5)) := superpose eq143 eq269 -- forward demodulation 269,143
  have eq333 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq305 eq332 -- forward demodulation 332,305
  have eq502 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = ((X4 ◇ (X6 ◇ X5)) ◇ (X6 ◇ (X0 ◇ X3))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2.2.2 in 17
  have eq519 (X0 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X3 ◇ (X2 ◇ X2))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2 in 17
  have eq572 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq17 eq502 -- forward demodulation 502,17
  have eq573 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X3))) = (X4 ◇ ((X0 ◇ X3) ◇ (X5 ◇ (X1 ◇ X1)))) := superpose eq333 eq572 -- forward demodulation 572,333
  have eq574 (X0 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ X3) ◇ X5)) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq279 eq573 -- forward demodulation 573,279
  have eq578 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq574 eq280 -- backward demodulation 280,574
  have eq585 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X2) := superpose eq574 eq12 -- backward demodulation 12,574
  have eq754 (X0 X1 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ X1)) := superpose eq519 eq578 -- backward demodulation 578,519
  have eq902 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq519 eq585 -- superposition 585,519, 519 into 585, unify on (0).2 in 519 and (0).2.1.2 in 585
  have eq966 (X0 X1 X3 : G) : ((X3 ◇ X1) ◇ X0) = (X3 ◇ (X0 ◇ X1)) := superpose eq754 eq902 -- forward demodulation 902,754
  have eq999 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X3)) = ((X0 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X2) := superpose eq966 eq585 -- backward demodulation 585,966
  have eq1458 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X1 ◇ X2)) := superpose eq9 eq999 -- superposition 999,9, 9 into 999, unify on (0).2 in 9 and (0).2 in 999
  have eq1553 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := superpose eq1458 eq10 -- superposition 10,1458, 1458 into 10, unify on (0).2 in 1458 and (0).2 in 10
  subsumption eq1553 eq58


@[equational_result]
theorem Equation3940_implies_Equation4477 (G : Type*) [Magma G] (h : Equation3940 G) : Equation4477 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) = ((X0 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X3 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq16 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) = ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ (X4 ◇ X1)) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.1 in 9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2 in 21
  have eq109 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X3))) = ((X5 ◇ (X0 ◇ X4)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2.1.2 in 9
  have eq134 (X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X3))) = (X5 ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq17 eq109 -- forward demodulation 109,17
  have eq143 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.1 in 58
  have eq192 (X1 X2 X3 X4 X5 : G) : (X5 ◇ (X1 ◇ (X4 ◇ X2))) = (X5 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X3)))) := superpose eq143 eq134 -- backward demodulation 134,143
  have eq261 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ ((X0 ◇ X2) ◇ X4)) ◇ X5) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.1.2.1 in 16
  have eq269 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ ((X0 ◇ X3) ◇ X1)) ◇ X5) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).1.1.2 in 16
  have eq279 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq12 eq16 -- superposition 16,12, 12 into 16, unify on (0).2 in 12 and (0).1 in 16
  have eq280 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1 in 16
  have eq303 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) := superpose eq143 eq261 -- forward demodulation 261,143
  have eq304 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X5 ◇ X1)))) := superpose eq143 eq303 -- forward demodulation 303,143
  have eq305 (X0 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ (X0 ◇ (X5 ◇ X2))) := superpose eq192 eq304 -- forward demodulation 304,192
  have eq332 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ ((X0 ◇ X3) ◇ X5)) := superpose eq143 eq269 -- forward demodulation 269,143
  have eq333 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq305 eq332 -- forward demodulation 332,305
  have eq502 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = ((X4 ◇ (X6 ◇ X5)) ◇ (X6 ◇ (X0 ◇ X3))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2.2.2 in 17
  have eq519 (X0 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X3 ◇ (X2 ◇ X2))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2 in 17
  have eq520 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X3))) := superpose eq21 eq17 -- superposition 17,21, 21 into 17, unify on (0).2 in 21 and (0).2 in 17
  have eq572 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq17 eq502 -- forward demodulation 502,17
  have eq573 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X3))) = (X4 ◇ ((X0 ◇ X3) ◇ (X5 ◇ (X1 ◇ X1)))) := superpose eq333 eq572 -- forward demodulation 572,333
  have eq574 (X0 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ X3) ◇ X5)) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq279 eq573 -- forward demodulation 573,279
  have eq578 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq574 eq280 -- backward demodulation 280,574
  have eq585 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X2) := superpose eq574 eq12 -- backward demodulation 12,574
  have eq754 (X0 X1 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ X1)) := superpose eq519 eq578 -- backward demodulation 578,519
  have eq755 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X3)))) := superpose eq574 eq520 -- forward demodulation 520,574
  have eq756 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ X2)) := superpose eq519 eq755 -- forward demodulation 755,519
  have eq810 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = (X0 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq17 eq519 -- superposition 519,17, 17 into 519, unify on (0).2 in 17 and (0).2 in 519
  have eq851 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq9 eq810 -- forward demodulation 810,9
  have eq902 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq519 eq585 -- superposition 585,519, 519 into 585, unify on (0).2 in 519 and (0).2.1.2 in 585
  have eq966 (X0 X1 X3 : G) : ((X3 ◇ X1) ◇ X0) = (X3 ◇ (X0 ◇ X1)) := superpose eq754 eq902 -- forward demodulation 902,754
  have eq967 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq966 eq21 -- backward demodulation 21,966
  have eq999 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X3)) = ((X0 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X2) := superpose eq966 eq585 -- backward demodulation 585,966
  have eq1458 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X1 ◇ X2)) := superpose eq9 eq999 -- superposition 999,9, 9 into 999, unify on (0).2 in 9 and (0).2 in 999
  have eq1690 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X3))) := superpose eq17 eq967 -- superposition 967,17, 17 into 967, unify on (0).2 in 17 and (0).1 in 967
  have eq1740 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3)))) := superpose eq1458 eq1690 -- forward demodulation 1690,1458
  have eq1741 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose eq851 eq1740 -- forward demodulation 1740,851
  have eq1836 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq756 eq10 -- superposition 10,756, 756 into 10, unify on (0).2 in 756 and (0).2 in 10
  subsumption eq1836 eq1741


@[equational_result]
theorem Equation3940_implies_Equation4146 (G : Type*) [Magma G] (h : Equation3940 G) : Equation4146 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) = ((X0 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X3 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq16 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) = ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ (X4 ◇ X1)) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.1 in 9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2 in 21
  have eq109 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X3))) = ((X5 ◇ (X0 ◇ X4)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2.1.2 in 9
  have eq134 (X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X3))) = (X5 ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq17 eq109 -- forward demodulation 109,17
  have eq143 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.1 in 58
  have eq161 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X2) ◇ X1) := superpose eq58 eq9 -- superposition 9,58, 58 into 9, unify on (0).2 in 58 and (0).2.1 in 9
  have eq192 (X1 X2 X3 X4 X5 : G) : (X5 ◇ (X1 ◇ (X4 ◇ X2))) = (X5 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X3)))) := superpose eq143 eq134 -- backward demodulation 134,143
  have eq261 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ ((X0 ◇ X2) ◇ X4)) ◇ X5) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.1.2.1 in 16
  have eq269 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ ((X0 ◇ X3) ◇ X1)) ◇ X5) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).1.1.2 in 16
  have eq279 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq12 eq16 -- superposition 16,12, 12 into 16, unify on (0).2 in 12 and (0).1 in 16
  have eq280 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1 in 16
  have eq303 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) := superpose eq143 eq261 -- forward demodulation 261,143
  have eq304 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X5 ◇ X1)))) := superpose eq143 eq303 -- forward demodulation 303,143
  have eq305 (X0 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ (X0 ◇ (X5 ◇ X2))) := superpose eq192 eq304 -- forward demodulation 304,192
  have eq332 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ ((X0 ◇ X3) ◇ X5)) := superpose eq143 eq269 -- forward demodulation 269,143
  have eq333 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq305 eq332 -- forward demodulation 332,305
  have eq426 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK1) ◇ sK2) := superpose eq161 eq10 -- superposition 10,161, 161 into 10, unify on (0).2 in 161 and (0).2 in 10
  have eq474 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK2) := superpose eq161 eq426 -- forward demodulation 426,161
  have eq506 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = ((X4 ◇ (X6 ◇ X5)) ◇ (X6 ◇ (X0 ◇ X3))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2.2.2 in 17
  have eq523 (X0 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X3 ◇ (X2 ◇ X2))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2 in 17
  have eq576 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq17 eq506 -- forward demodulation 506,17
  have eq577 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X3))) = (X4 ◇ ((X0 ◇ X3) ◇ (X5 ◇ (X1 ◇ X1)))) := superpose eq333 eq576 -- forward demodulation 576,333
  have eq578 (X0 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ X3) ◇ X5)) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq279 eq577 -- forward demodulation 577,279
  have eq582 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq578 eq280 -- backward demodulation 280,578
  have eq589 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X2) := superpose eq578 eq12 -- backward demodulation 12,578
  have eq758 (X0 X1 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ X1)) := superpose eq523 eq582 -- backward demodulation 582,523
  have eq906 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq523 eq589 -- superposition 589,523, 523 into 589, unify on (0).2 in 523 and (0).2.1.2 in 589
  have eq970 (X0 X1 X3 : G) : ((X3 ◇ X1) ◇ X0) = (X3 ◇ (X0 ◇ X1)) := superpose eq758 eq906 -- forward demodulation 906,758
  have eq1120 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK2) := superpose eq970 eq474 -- backward demodulation 474,970
  subsumption eq1120 eq9


@[equational_result]
theorem Equation3940_implies_Equation4120 (G : Type*) [Magma G] (h : Equation3940 G) : Equation4120 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) = ((X0 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X3 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq16 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) = ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ (X4 ◇ X1)) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.1 in 9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2 in 21
  have eq82 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) = ((X0 ◇ X3) ◇ ((X1 ◇ (X5 ◇ X2)) ◇ (X4 ◇ X5))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq117 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) = ((X0 ◇ X3) ◇ ((X1 ◇ (X5 ◇ X2)) ◇ (X4 ◇ X5))) := superpose eq16 eq82 -- forward demodulation 82,16
  have eq143 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.1 in 58
  have eq194 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) = ((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ (X5 ◇ (X4 ◇ X5)))) := superpose eq143 eq117 -- backward demodulation 117,143
  have eq261 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ ((X0 ◇ X2) ◇ X4)) ◇ X5) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.1.2.1 in 16
  have eq269 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ ((X0 ◇ X3) ◇ X1)) ◇ X5) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).1.1.2 in 16
  have eq279 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq12 eq16 -- superposition 16,12, 12 into 16, unify on (0).2 in 12 and (0).1 in 16
  have eq280 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1 in 16
  have eq303 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) := superpose eq143 eq261 -- forward demodulation 261,143
  have eq304 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X5 ◇ X1)))) := superpose eq143 eq303 -- forward demodulation 303,143
  have eq305 (X0 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ (X0 ◇ (X5 ◇ X2))) := superpose eq194 eq304 -- forward demodulation 304,194
  have eq332 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ ((X0 ◇ X3) ◇ X5)) := superpose eq143 eq269 -- forward demodulation 269,143
  have eq333 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq305 eq332 -- forward demodulation 332,305
  have eq504 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = ((X4 ◇ (X6 ◇ X5)) ◇ (X6 ◇ (X0 ◇ X3))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2.2.2 in 17
  have eq521 (X0 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X3 ◇ (X2 ◇ X2))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2 in 17
  have eq574 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq17 eq504 -- forward demodulation 504,17
  have eq575 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X3))) = (X4 ◇ ((X0 ◇ X3) ◇ (X5 ◇ (X1 ◇ X1)))) := superpose eq333 eq574 -- forward demodulation 574,333
  have eq576 (X0 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ X3) ◇ X5)) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq279 eq575 -- forward demodulation 575,279
  have eq580 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq576 eq280 -- backward demodulation 280,576
  have eq587 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X2) := superpose eq576 eq12 -- backward demodulation 12,576
  have eq756 (X0 X1 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ X1)) := superpose eq521 eq580 -- backward demodulation 580,521
  have eq905 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq521 eq587 -- superposition 587,521, 521 into 587, unify on (0).2 in 521 and (0).2.1.2 in 587
  have eq969 (X0 X1 X3 : G) : ((X3 ◇ X1) ◇ X0) = (X3 ◇ (X0 ◇ X1)) := superpose eq756 eq905 -- forward demodulation 905,756
  have eq1002 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X3)) = ((X0 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X2) := superpose eq969 eq587 -- backward demodulation 587,969
  have eq1119 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq969 eq10 -- backward demodulation 10,969
  have eq1416 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X1 ◇ X2)) := superpose eq9 eq1002 -- superposition 1002,9, 9 into 1002, unify on (0).2 in 9 and (0).2 in 1002
  have eq1454 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq1416 eq1119 -- backward demodulation 1119,1416
  subsumption eq1454 eq9


@[equational_result]
theorem Equation3940_implies_Equation4071 (G : Type*) [Magma G] (h : Equation3940 G) : Equation4071 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) = ((X0 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.1 in 9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2 in 21
  have eq59 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ X2) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq12 eq21 -- superposition 21,12, 12 into 21, unify on (0).2 in 12 and (0).2 in 21
  have eq164 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X2) ◇ X1) := superpose eq58 eq9 -- superposition 9,58, 58 into 9, unify on (0).2 in 58 and (0).2.1 in 9
  have eq251 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq164 eq10 -- backward demodulation 10,164
  have eq511 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X1) := superpose eq11 eq59 -- superposition 59,11, 11 into 59, unify on (0).2 in 11 and (0).2 in 59
  have eq734 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := superpose eq511 eq251 -- backward demodulation 251,511
  subsumption eq734 eq9


@[equational_result]
theorem Equation3940_implies_Equation4068 (G : Type*) [Magma G] (h : Equation3940 G) : Equation4068 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) = ((X0 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X3 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq16 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) = ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ (X4 ◇ X1)) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.1 in 9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2 in 21
  have eq82 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) = ((X0 ◇ X3) ◇ ((X1 ◇ (X5 ◇ X2)) ◇ (X4 ◇ X5))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq117 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) = ((X0 ◇ X3) ◇ ((X1 ◇ (X5 ◇ X2)) ◇ (X4 ◇ X5))) := superpose eq16 eq82 -- forward demodulation 82,16
  have eq143 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.1 in 58
  have eq194 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) = ((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ (X5 ◇ (X4 ◇ X5)))) := superpose eq143 eq117 -- backward demodulation 117,143
  have eq261 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ ((X0 ◇ X2) ◇ X4)) ◇ X5) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.1.2.1 in 16
  have eq269 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ ((X0 ◇ X3) ◇ X1)) ◇ X5) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).1.1.2 in 16
  have eq279 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq12 eq16 -- superposition 16,12, 12 into 16, unify on (0).2 in 12 and (0).1 in 16
  have eq280 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1 in 16
  have eq303 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) := superpose eq143 eq261 -- forward demodulation 261,143
  have eq304 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X5 ◇ X1)))) := superpose eq143 eq303 -- forward demodulation 303,143
  have eq305 (X0 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ (X0 ◇ (X5 ◇ X2))) := superpose eq194 eq304 -- forward demodulation 304,194
  have eq332 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ ((X0 ◇ X3) ◇ X5)) := superpose eq143 eq269 -- forward demodulation 269,143
  have eq333 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq305 eq332 -- forward demodulation 332,305
  have eq502 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = ((X4 ◇ (X6 ◇ X5)) ◇ (X6 ◇ (X0 ◇ X3))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2.2.2 in 17
  have eq519 (X0 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X3 ◇ (X2 ◇ X2))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2 in 17
  have eq572 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq17 eq502 -- forward demodulation 502,17
  have eq573 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X3))) = (X4 ◇ ((X0 ◇ X3) ◇ (X5 ◇ (X1 ◇ X1)))) := superpose eq333 eq572 -- forward demodulation 572,333
  have eq574 (X0 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ X3) ◇ X5)) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq279 eq573 -- forward demodulation 573,279
  have eq578 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq574 eq280 -- backward demodulation 280,574
  have eq585 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X2) := superpose eq574 eq12 -- backward demodulation 12,574
  have eq754 (X0 X1 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ X1)) := superpose eq519 eq578 -- backward demodulation 578,519
  have eq903 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq519 eq585 -- superposition 585,519, 519 into 585, unify on (0).2 in 519 and (0).2.1.2 in 585
  have eq967 (X0 X1 X3 : G) : ((X3 ◇ X1) ◇ X0) = (X3 ◇ (X0 ◇ X1)) := superpose eq754 eq903 -- forward demodulation 903,754
  have eq1116 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := superpose eq967 eq10 -- backward demodulation 10,967
  subsumption eq1116 eq9


@[equational_result]
theorem Equation3940_implies_Equation4135 (G : Type*) [Magma G] (h : Equation3940 G) : Equation4135 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) = ((X0 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X3 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq16 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) = ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ (X4 ◇ X1)) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.1 in 9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2 in 21
  have eq82 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) = ((X0 ◇ X3) ◇ ((X1 ◇ (X5 ◇ X2)) ◇ (X4 ◇ X5))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq117 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) = ((X0 ◇ X3) ◇ ((X1 ◇ (X5 ◇ X2)) ◇ (X4 ◇ X5))) := superpose eq16 eq82 -- forward demodulation 82,16
  have eq143 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.1 in 58
  have eq194 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) = ((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ (X5 ◇ (X4 ◇ X5)))) := superpose eq143 eq117 -- backward demodulation 117,143
  have eq261 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ ((X0 ◇ X2) ◇ X4)) ◇ X5) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.1.2.1 in 16
  have eq269 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ ((X0 ◇ X3) ◇ X1)) ◇ X5) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).1.1.2 in 16
  have eq279 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq12 eq16 -- superposition 16,12, 12 into 16, unify on (0).2 in 12 and (0).1 in 16
  have eq280 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1 in 16
  have eq303 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) := superpose eq143 eq261 -- forward demodulation 261,143
  have eq304 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X5 ◇ X1)))) := superpose eq143 eq303 -- forward demodulation 303,143
  have eq305 (X0 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ (X0 ◇ (X5 ◇ X2))) := superpose eq194 eq304 -- forward demodulation 304,194
  have eq332 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ ((X0 ◇ X3) ◇ X5)) := superpose eq143 eq269 -- forward demodulation 269,143
  have eq333 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq305 eq332 -- forward demodulation 332,305
  have eq502 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = ((X4 ◇ (X6 ◇ X5)) ◇ (X6 ◇ (X0 ◇ X3))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2.2.2 in 17
  have eq519 (X0 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X3 ◇ (X2 ◇ X2))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2 in 17
  have eq572 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq17 eq502 -- forward demodulation 502,17
  have eq573 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X3))) = (X4 ◇ ((X0 ◇ X3) ◇ (X5 ◇ (X1 ◇ X1)))) := superpose eq333 eq572 -- forward demodulation 572,333
  have eq574 (X0 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ X3) ◇ X5)) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq279 eq573 -- forward demodulation 573,279
  have eq578 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq574 eq280 -- backward demodulation 280,574
  have eq585 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X2) := superpose eq574 eq12 -- backward demodulation 12,574
  have eq754 (X0 X1 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ X1)) := superpose eq519 eq578 -- backward demodulation 578,519
  have eq903 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq519 eq585 -- superposition 585,519, 519 into 585, unify on (0).2 in 519 and (0).2.1.2 in 585
  have eq967 (X0 X1 X3 : G) : ((X3 ◇ X1) ◇ X0) = (X3 ◇ (X0 ◇ X1)) := superpose eq754 eq903 -- forward demodulation 903,754
  have eq1116 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK2) := superpose eq967 eq10 -- backward demodulation 10,967
  subsumption eq1116 eq9


@[equational_result]
theorem Equation3940_implies_Equation3737 (G : Type*) [Magma G] (h : Equation3940 G) : Equation3737 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) = ((X0 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X3 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq16 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) = ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ (X4 ◇ X1)) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.1 in 9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2 in 21
  have eq109 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X3))) = ((X5 ◇ (X0 ◇ X4)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2.1.2 in 9
  have eq134 (X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X3))) = (X5 ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq17 eq109 -- forward demodulation 109,17
  have eq143 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.1 in 58
  have eq192 (X1 X2 X3 X4 X5 : G) : (X5 ◇ (X1 ◇ (X4 ◇ X2))) = (X5 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X3)))) := superpose eq143 eq134 -- backward demodulation 134,143
  have eq261 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ ((X0 ◇ X2) ◇ X4)) ◇ X5) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.1.2.1 in 16
  have eq269 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ ((X0 ◇ X3) ◇ X1)) ◇ X5) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).1.1.2 in 16
  have eq279 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq12 eq16 -- superposition 16,12, 12 into 16, unify on (0).2 in 12 and (0).1 in 16
  have eq280 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1 in 16
  have eq303 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) := superpose eq143 eq261 -- forward demodulation 261,143
  have eq304 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X5 ◇ X1)))) := superpose eq143 eq303 -- forward demodulation 303,143
  have eq305 (X0 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ (X0 ◇ (X5 ◇ X2))) := superpose eq192 eq304 -- forward demodulation 304,192
  have eq332 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ ((X0 ◇ X3) ◇ X5)) := superpose eq143 eq269 -- forward demodulation 269,143
  have eq333 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq305 eq332 -- forward demodulation 332,305
  have eq502 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = ((X4 ◇ (X6 ◇ X5)) ◇ (X6 ◇ (X0 ◇ X3))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2.2.2 in 17
  have eq519 (X0 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X3 ◇ (X2 ◇ X2))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2 in 17
  have eq572 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq17 eq502 -- forward demodulation 502,17
  have eq573 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X3))) = (X4 ◇ ((X0 ◇ X3) ◇ (X5 ◇ (X1 ◇ X1)))) := superpose eq333 eq572 -- forward demodulation 572,333
  have eq574 (X0 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ X3) ◇ X5)) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq279 eq573 -- forward demodulation 573,279
  have eq578 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq574 eq280 -- backward demodulation 280,574
  have eq585 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X2) := superpose eq574 eq12 -- backward demodulation 12,574
  have eq754 (X0 X1 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ X1)) := superpose eq519 eq578 -- backward demodulation 578,519
  have eq902 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq519 eq585 -- superposition 585,519, 519 into 585, unify on (0).2 in 519 and (0).2.1.2 in 585
  have eq966 (X0 X1 X3 : G) : ((X3 ◇ X1) ◇ X0) = (X3 ◇ (X0 ◇ X1)) := superpose eq754 eq902 -- forward demodulation 902,754
  have eq3974 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := superpose eq966 eq10 -- superposition 10,966, 966 into 10, unify on (0).2 in 966 and (0).2 in 10
  have eq4064 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := superpose eq966 eq3974 -- forward demodulation 3974,966
  subsumption eq4064 eq519


