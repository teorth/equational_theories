import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation2893_implies_Equation2671 (G : Type*) [Magma G] (h : Equation2893 G) : Equation2671 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (((X4 ◇ X0) ◇ X3) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation3098_implies_Equation3262 (G : Type*) [Magma G] (h : Equation3098 G) : Equation3262 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation3098_implies_Equation3458 (G : Type*) [Magma G] (h : Equation3098 G) : Equation3458 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ X0) ◇ sK0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.1 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation3071_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3071 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq11


@[equational_result]
theorem Equation3071_implies_Equation307 (G : Type*) [Magma G] (h : Equation3071 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq14 rfl


@[equational_result]
theorem Equation3071_implies_Equation3306 (G : Type*) [Magma G] (h : Equation3071 G) : Equation3306 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3071_implies_Equation323 (G : Type*) [Magma G] (h : Equation3071 G) : Equation323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation125_implies_Equation73 (G : Type*) [Magma G] (h : Equation125 G) : Equation73 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq14 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq14 rfl


@[equational_result]
theorem Equation125_implies_Equation229 (G : Type*) [Magma G] (h : Equation125 G) : Equation229 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq16 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq19 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := superpose eq11 eq16 -- forward demodulation 16,11
  subsumption eq19 eq12


@[equational_result]
theorem Equation125_implies_Equation4435 (G : Type*) [Magma G] (h : Equation125 G) : Equation4435 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation2062_implies_Equation3255 (G : Type*) [Magma G] (h : Equation2062 G) : Equation3255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X1) = (((((X0 ◇ X1) ◇ X1) ◇ X3) ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1.1 in 13
  have eq27 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.1 in 13
  have eq32 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq9 eq27 -- forward demodulation 27,9
  have eq34 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq32 eq9 -- superposition 9,32, 32 into 9, unify on (0).2 in 32 and (0).1.1 in 9
  have eq56 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.2 in 12
  have eq85 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X3) ◇ X3) := superpose eq24 eq24 -- superposition 24,24, 24 into 24, unify on (0).2 in 24 and (0).2 in 24
  have eq147 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq85 eq34 -- superposition 34,85, 85 into 34, unify on (0).2 in 85 and (0).2.2 in 34
  have eq211 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq147 eq56 -- backward demodulation 56,147
  have eq307 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq211 eq10 -- superposition 10,211, 211 into 10, unify on (0).2 in 211 and (0).2 in 10
  subsumption eq307 rfl


@[equational_result]
theorem Equation2062_implies_Equation4598 (G : Type*) [Magma G] (h : Equation2062 G) : Equation4598 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X1) = (((((X0 ◇ X1) ◇ X1) ◇ X3) ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1.1 in 13
  have eq27 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.1 in 13
  have eq32 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq9 eq27 -- forward demodulation 27,9
  have eq85 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X3) ◇ X3) := superpose eq24 eq24 -- superposition 24,24, 24 into 24, unify on (0).2 in 24 and (0).2 in 24
  have eq125 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq32 eq85 -- superposition 85,32, 32 into 85, unify on (0).2 in 32 and (0).1 in 85
  have eq362 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) ◇ X0) := superpose eq125 eq9 -- superposition 9,125, 125 into 9, unify on (0).2 in 125 and (0).1.2 in 9
  have eq364 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq125 eq85 -- superposition 85,125, 125 into 85, unify on (0).2 in 125 and (0).1.1 in 85
  have eq373 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq364 eq362 -- backward demodulation 362,364
  have eq1084 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq373 eq10 -- superposition 10,373, 373 into 10, unify on (0).2 in 373 and (0).2 in 10
  subsumption eq1084 rfl


@[equational_result]
theorem Equation2077_implies_Equation2874 (G : Type*) [Magma G] (h : Equation2077 G) : Equation2874 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 X1 X2 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X4) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq27 (X0 X1 : G) : sK0 ≠ (((sK0 ◇ (X0 ◇ X1)) ◇ sK0) ◇ sK2) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1.1 in 10
  subsumption eq27 eq20


@[equational_result]
theorem Equation829_implies_Equation3918 (G : Type*) [Magma G] (h : Equation829 G) : Equation3918 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.2 in 13
  have eq21 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq21 rfl


@[equational_result]
theorem Equation829_implies_Equation423 (G : Type*) [Magma G] (h : Equation829 G) : Equation423 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation829_implies_Equation308 (G : Type*) [Magma G] (h : Equation829 G) : Equation308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.2 in 13
  have eq16 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq21 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq27 : sK0 ≠ sK0 := superpose eq16 eq21 -- superposition 21,16, 16 into 21, unify on (0).2 in 16 and (0).2 in 21
  subsumption eq27 rfl


@[equational_result]
theorem Equation829_implies_Equation1026 (G : Type*) [Magma G] (h : Equation829 G) : Equation1026 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq59 (X0 X1 X4 : G) : (X4 ◇ ((X4 ◇ (X0 ◇ X1)) ◇ X0)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.2 in 12
  have eq120 : sK0 ≠ sK0 := superpose eq59 eq10 -- superposition 10,59, 59 into 10, unify on (0).2 in 59 and (0).2 in 10
  subsumption eq120 rfl


@[equational_result]
theorem Equation829_implies_Equation1032 (G : Type*) [Magma G] (h : Equation829 G) : Equation1032 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq59 (X0 X1 X4 : G) : (X4 ◇ ((X4 ◇ (X0 ◇ X1)) ◇ X0)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.2 in 12
  have eq120 : sK0 ≠ sK0 := superpose eq59 eq10 -- superposition 10,59, 59 into 10, unify on (0).2 in 59 and (0).2 in 10
  subsumption eq120 rfl


@[equational_result]
theorem Equation215_implies_Equation1428 (G : Type*) [Magma G] (h : Equation215 G) : Equation1428 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation215_implies_Equation1452 (G : Type*) [Magma G] (h : Equation215 G) : Equation1452 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation215_implies_Equation3520 (G : Type*) [Magma G] (h : Equation215 G) : Equation3520 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq33 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq33 rfl


@[equational_result]
theorem Equation215_implies_Equation3525 (G : Type*) [Magma G] (h : Equation215 G) : Equation3525 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq33 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq33 rfl


@[equational_result]
theorem Equation215_implies_Equation1430 (G : Type*) [Magma G] (h : Equation215 G) : Equation1430 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation215_implies_Equation159 (G : Type*) [Magma G] (h : Equation215 G) : Equation159 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ (X4 ◇ X0)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq44 : sK0 ≠ sK0 := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq44 rfl


@[equational_result]
theorem Equation215_implies_Equation3524 (G : Type*) [Magma G] (h : Equation215 G) : Equation3524 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq33 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq33 rfl


@[equational_result]
theorem Equation215_implies_Equation4357 (G : Type*) [Magma G] (h : Equation215 G) : Equation4357 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq21 (X0 X1 X4 X5 : G) : (X4 ◇ (X0 ◇ X1)) = (X4 ◇ (X0 ◇ X5)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.2.1 in 12
  have eq87 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq87 eq21


@[equational_result]
theorem Equation215_implies_Equation3521 (G : Type*) [Magma G] (h : Equation215 G) : Equation3521 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq33 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq33 rfl


@[equational_result]
theorem Equation215_implies_Equation1457 (G : Type*) [Magma G] (h : Equation215 G) : Equation1457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation3904_implies_Equation3693 (G : Type*) [Magma G] (h : Equation3904 G) : Equation3693 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X1)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq15 (X3 X4 X5 : G) : (X4 ◇ X4) = ((X3 ◇ X3) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq29 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (sK2 ◇ sK3)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1 in 10
  subsumption eq29 eq15


@[equational_result]
theorem Equation3904_implies_Equation3879 (G : Type*) [Magma G] (h : Equation3904 G) : Equation3879 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X1)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq14 (X2 X3 X4 X5 : G) : (X4 ◇ X4) = ((X2 ◇ (X3 ◇ X3)) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq29 (X0 : G) : (X0 ◇ X0) ≠ ((sK1 ◇ (X0 ◇ X0)) ◇ sK2) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).1 in 10
  subsumption eq29 eq14


@[equational_result]
theorem Equation86_implies_Equation1441 (G : Type*) [Magma G] (h : Equation86 G) : Equation1441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq22 (X0 : G) : sK0 ≠ ((X0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq22 eq13


@[equational_result]
theorem Equation86_implies_Equation1431 (G : Type*) [Magma G] (h : Equation86 G) : Equation1431 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq22 (X0 : G) : sK0 ≠ (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 eq13


@[equational_result]
theorem Equation86_implies_Equation361 (G : Type*) [Magma G] (h : Equation86 G) : Equation361 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ sK1) ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq19 eq12


@[equational_result]
theorem Equation86_implies_Equation3864 (G : Type*) [Magma G] (h : Equation86 G) : Equation3864 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK0 ◇ (X0 ◇ sK1)) ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1.2 in 10
  subsumption eq22 eq12


@[equational_result]
theorem Equation86_implies_Equation860 (G : Type*) [Magma G] (h : Equation86 G) : Equation860 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq22 (X0 : G) : sK0 ≠ (sK0 ◇ (X0 ◇ (sK2 ◇ sK0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq22 eq13


@[equational_result]
theorem Equation86_implies_Equation4165 (G : Type*) [Magma G] (h : Equation86 G) : Equation4165 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 (X0 : G) : (sK0 ◇ sK1) ≠ (((X0 ◇ sK1) ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1.1 in 10
  subsumption eq22 eq12


@[equational_result]
theorem Equation2791_implies_Equation2246 (G : Type*) [Magma G] (h : Equation2791 G) : Equation2246 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ X3) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq53 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X0))) ◇ X3) = X3 := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).1.1.2.2 in 14
  have eq56 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3) = X3 := superpose eq15 eq53 -- forward demodulation 53,15
  have eq99 : sK0 ≠ sK0 := superpose eq56 eq10 -- superposition 10,56, 56 into 10, unify on (0).2 in 56 and (0).2 in 10
  subsumption eq99 rfl


@[equational_result]
theorem Equation2791_implies_Equation3759 (G : Type*) [Magma G] (h : Equation2791 G) : Equation3759 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq52 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq52 rfl


@[equational_result]
theorem Equation2791_implies_Equation3152 (G : Type*) [Magma G] (h : Equation2791 G) : Equation3152 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq22 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq22 eq15


@[equational_result]
theorem Equation2791_implies_Equation4622 (G : Type*) [Magma G] (h : Equation2791 G) : Equation4622 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq22 : sK1 ≠ ((sK2 ◇ sK2) ◇ sK1) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq22 eq15


@[equational_result]
theorem Equation2791_implies_Equation2496 (G : Type*) [Magma G] (h : Equation2791 G) : Equation2496 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq22 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq22 eq15


@[equational_result]
theorem Equation2791_implies_Equation3139 (G : Type*) [Magma G] (h : Equation2791 G) : Equation3139 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq22 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq22 eq15


@[equational_result]
theorem Equation2791_implies_Equation211 (G : Type*) [Magma G] (h : Equation2791 G) : Equation211 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ X3) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq31 (X0 X3 X4 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ X4) = X4 := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq70 : sK0 ≠ sK0 := superpose eq31 eq10 -- superposition 10,31, 31 into 10, unify on (0).2 in 31 and (0).2 in 10
  subsumption eq70 rfl


@[equational_result]
theorem Equation2791_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2791 G) : Equation2441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq14 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).1.1.1 in 12
  have eq21 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq14 eq9 -- backward demodulation 9,14
  subsumption eq21 eq14


@[equational_result]
theorem Equation2791_implies_Equation2770 (G : Type*) [Magma G] (h : Equation2791 G) : Equation2770 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ X3) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq31 (X0 X3 X4 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ X4) = X4 := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq70 : sK0 ≠ sK0 := superpose eq31 eq10 -- superposition 10,31, 31 into 10, unify on (0).2 in 31 and (0).2 in 10
  subsumption eq70 rfl


@[equational_result]
theorem Equation2791_implies_Equation3456 (G : Type*) [Magma G] (h : Equation2791 G) : Equation3456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq14 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).1.1.1 in 12
  have eq21 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq14 eq9 -- backward demodulation 9,14
  subsumption eq21 rfl


@[equational_result]
theorem Equation2791_implies_Equation2687 (G : Type*) [Magma G] (h : Equation2791 G) : Equation2687 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ X3) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq31 (X0 X3 X4 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ X4) = X4 := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq70 : sK0 ≠ sK0 := superpose eq31 eq10 -- superposition 10,31, 31 into 10, unify on (0).2 in 31 and (0).2 in 10
  subsumption eq70 rfl


@[equational_result]
theorem Equation2791_implies_Equation23 (G : Type*) [Magma G] (h : Equation2791 G) : Equation23 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq14 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).1.1.1 in 12
  have eq55 : sK0 ≠ sK0 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2 in 9
  subsumption eq55 rfl


@[equational_result]
theorem Equation2791_implies_Equation1629 (G : Type*) [Magma G] (h : Equation2791 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq14 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).1.1.1 in 12
  have eq21 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq14 eq9 -- backward demodulation 9,14
  subsumption eq21 eq14


@[equational_result]
theorem Equation2791_implies_Equation4118 (G : Type*) [Magma G] (h : Equation2791 G) : Equation4118 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq22 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq22 rfl


@[equational_result]
theorem Equation2791_implies_Equation2733 (G : Type*) [Magma G] (h : Equation2791 G) : Equation2733 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq22 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq22 eq15


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
theorem Equation2791_implies_Equation3509 (G : Type*) [Magma G] (h : Equation2791 G) : Equation3509 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq22 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq22 rfl


@[equational_result]
theorem Equation2791_implies_Equation4226 (G : Type*) [Magma G] (h : Equation2791 G) : Equation4226 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK2) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq22 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq22 rfl


@[equational_result]
theorem Equation2791_implies_Equation2466 (G : Type*) [Magma G] (h : Equation2791 G) : Equation2466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq22 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq22 eq15


@[equational_result]
theorem Equation2791_implies_Equation3058 (G : Type*) [Magma G] (h : Equation2791 G) : Equation3058 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq22 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq22 eq15


@[equational_result]
theorem Equation2791_implies_Equation2672 (G : Type*) [Magma G] (h : Equation2791 G) : Equation2672 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ X3) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq31 (X0 X3 X4 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ X4) = X4 := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1.2 in 14
  have eq77 : sK0 ≠ sK0 := superpose eq31 eq10 -- superposition 10,31, 31 into 10, unify on (0).2 in 31 and (0).2 in 10
  subsumption eq77 rfl


@[equational_result]
theorem Equation2791_implies_Equation4065 (G : Type*) [Magma G] (h : Equation2791 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq14 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).1.1.1 in 12
  have eq21 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq14 eq9 -- backward demodulation 9,14
  subsumption eq21 rfl


@[equational_result]
theorem Equation2791_implies_Equation2543 (G : Type*) [Magma G] (h : Equation2791 G) : Equation2543 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq22 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq22 eq15


@[equational_result]
theorem Equation2791_implies_Equation203 (G : Type*) [Magma G] (h : Equation2791 G) : Equation203 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) ◇ X3) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ X3) = X3 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq30 (X0 X3 X4 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ X4) = X4 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.2 in 13
  have eq69 : sK0 ≠ sK0 := superpose eq30 eq9 -- superposition 9,30, 30 into 9, unify on (0).2 in 30 and (0).2 in 9
  subsumption eq69 rfl


@[equational_result]
theorem Equation2791_implies_Equation3464 (G : Type*) [Magma G] (h : Equation2791 G) : Equation3464 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq22 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq22 rfl


@[equational_result]
theorem Equation2791_implies_Equation2355 (G : Type*) [Magma G] (h : Equation2791 G) : Equation2355 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ X3) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq53 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X0))) ◇ X3) = X3 := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).1.1.2.2 in 14
  have eq56 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3) = X3 := superpose eq15 eq53 -- forward demodulation 53,15
  have eq99 : sK0 ≠ sK0 := superpose eq56 eq10 -- superposition 10,56, 56 into 10, unify on (0).2 in 56 and (0).2 in 10
  subsumption eq99 rfl


@[equational_result]
theorem Equation2791_implies_Equation2340 (G : Type*) [Magma G] (h : Equation2791 G) : Equation2340 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ X3) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq53 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X0))) ◇ X3) = X3 := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).1.1.2.2 in 14
  have eq56 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3) = X3 := superpose eq15 eq53 -- forward demodulation 53,15
  have eq99 : sK0 ≠ sK0 := superpose eq56 eq10 -- superposition 10,56, 56 into 10, unify on (0).2 in 56 and (0).2 in 10
  subsumption eq99 rfl


@[equational_result]
theorem Equation3476_implies_Equation3674 (G : Type*) [Magma G] (h : Equation3476 G) : Equation3674 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq22 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq29 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq29 eq22


@[equational_result]
theorem Equation3476_implies_Equation3288 (G : Type*) [Magma G] (h : Equation3476 G) : Equation3288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq33 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq33 eq15


@[equational_result]
theorem Equation3476_implies_Equation312 (G : Type*) [Magma G] (h : Equation3476 G) : Equation312 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq22 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq33 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq33 eq22


@[equational_result]
theorem Equation3476_implies_Equation3498 (G : Type*) [Magma G] (h : Equation3476 G) : Equation3498 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK3)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq50 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq50 eq23


@[equational_result]
theorem Equation3476_implies_Equation3473 (G : Type*) [Magma G] (h : Equation3476 G) : Equation3473 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq22 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq88 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq22 eq9 -- superposition 9,22, 22 into 9, unify on (0).2 in 22 and (0).2.2.1 in 9
  have eq93 (X0 : G) : (X0 ◇ X0) ≠ (sK1 ◇ ((X0 ◇ X0) ◇ sK2)) := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).1 in 10
  subsumption eq93 eq88


@[equational_result]
theorem Equation3476_implies_Equation3472 (G : Type*) [Magma G] (h : Equation3476 G) : Equation3472 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq22 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq88 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq22 eq9 -- superposition 9,22, 22 into 9, unify on (0).2 in 22 and (0).2.2.1 in 9
  have eq93 (X0 : G) : (X0 ◇ X0) ≠ (sK1 ◇ ((X0 ◇ X0) ◇ sK1)) := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).1 in 10
  subsumption eq93 eq88


@[equational_result]
theorem Equation3476_implies_Equation40 (G : Type*) [Magma G] (h : Equation3476 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq22 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq83 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).2 in 10
  subsumption eq83 eq22


@[equational_result]
theorem Equation3476_implies_Equation3496 (G : Type*) [Magma G] (h : Equation3476 G) : Equation3496 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq50 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq50 eq23


@[equational_result]
theorem Equation3476_implies_Equation3497 (G : Type*) [Magma G] (h : Equation3476 G) : Equation3497 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq50 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq50 eq23


@[equational_result]
theorem Equation3476_implies_Equation3462 (G : Type*) [Magma G] (h : Equation3476 G) : Equation3462 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq50 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq50 eq23


@[equational_result]
theorem Equation3476_implies_Equation3484 (G : Type*) [Magma G] (h : Equation3476 G) : Equation3484 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq44 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq44 eq23


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
theorem Equation3096_implies_Equation3076 (G : Type*) [Magma G] (h : Equation3096 G) : Equation3076 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq21 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X3) ◇ X2) ◇ X4) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq24 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ X0) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq24 eq21


@[equational_result]
theorem Equation3096_implies_Equation3523 (G : Type*) [Magma G] (h : Equation3096 G) : Equation3523 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq21 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ X0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  subsumption eq21 eq13


@[equational_result]
theorem Equation3096_implies_Equation3074 (G : Type*) [Magma G] (h : Equation3096 G) : Equation3074 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq21 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X3) ◇ X2) ◇ X4) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq24 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK1) ◇ X0) ◇ sK2) ◇ sK3) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq24 eq21


@[equational_result]
theorem Equation3096_implies_Equation3258 (G : Type*) [Magma G] (h : Equation3096 G) : Equation3258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 : G) : (sK0 ◇ X0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ X0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).1 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation4243_implies_Equation4689 (G : Type*) [Magma G] (h : Equation4243 G) : Equation4689 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK3 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (X3 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 : ((sK3 ◇ sK1) ◇ sK2) ≠ (sK1 ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation4243_implies_Equation4666 (G : Type*) [Magma G] (h : Equation4243 G) : Equation4666 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (X3 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 : ((sK2 ◇ sK1) ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation4243_implies_Equation364 (G : Type*) [Magma G] (h : Equation4243 G) : Equation364 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (X3 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation4243_implies_Equation3989 (G : Type*) [Magma G] (h : Equation4243 G) : Equation3989 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (X3 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation4243_implies_Equation3935 (G : Type*) [Magma G] (h : Equation4243 G) : Equation3935 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (X3 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation4243_implies_Equation3972 (G : Type*) [Magma G] (h : Equation4243 G) : Equation3972 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (X3 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation4243_implies_Equation3962 (G : Type*) [Magma G] (h : Equation4243 G) : Equation3962 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (X3 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation4243_implies_Equation4006 (G : Type*) [Magma G] (h : Equation4243 G) : Equation4006 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (X3 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation4243_implies_Equation385 (G : Type*) [Magma G] (h : Equation4243 G) : Equation385 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (X3 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation4243_implies_Equation3897 (G : Type*) [Magma G] (h : Equation4243 G) : Equation3897 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (X3 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 : (sK0 ◇ sK0) ≠ ((sK2 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation4243_implies_Equation3952 (G : Type*) [Magma G] (h : Equation4243 G) : Equation3952 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (X3 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation4243_implies_Equation3925 (G : Type*) [Magma G] (h : Equation4243 G) : Equation3925 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (X3 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation4243_implies_Equation4023 (G : Type*) [Magma G] (h : Equation4243 G) : Equation4023 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (X3 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation4243_implies_Equation4040 (G : Type*) [Magma G] (h : Equation4243 G) : Equation4040 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (X3 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK3 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 eq12


@[equational_result]
theorem Equation4243_implies_Equation395 (G : Type*) [Magma G] (h : Equation4243 G) : Equation395 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (X3 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1271_implies_Equation1241 (G : Type*) [Magma G] (h : Equation1271 G) : Equation1241 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X0 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq81 : sK0 ≠ sK0 := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq81 rfl


@[equational_result]
theorem Equation1271_implies_Equation1265 (G : Type*) [Magma G] (h : Equation1271 G) : Equation1265 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK1) ◇ sK3)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X0 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq81 : sK0 ≠ sK0 := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq81 rfl


@[equational_result]
theorem Equation3087_implies_Equation3077 (G : Type*) [Magma G] (h : Equation3087 G) : Equation3077 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK0) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq22 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X3) = X0 := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1 in 16
  have eq40 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ X0) ◇ sK0) ◇ sK2) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2.1.1 in 15
  subsumption eq40 eq22


@[equational_result]
theorem Equation3087_implies_Equation3457 (G : Type*) [Magma G] (h : Equation3087 G) : Equation3457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation3087_implies_Equation3262 (G : Type*) [Magma G] (h : Equation3087 G) : Equation3262 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation3087_implies_Equation329 (G : Type*) [Magma G] (h : Equation3087 G) : Equation329 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation3087_implies_Equation3261 (G : Type*) [Magma G] (h : Equation3087 G) : Equation3261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation3087_implies_Equation3317 (G : Type*) [Magma G] (h : Equation3087 G) : Equation3317 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation3273_implies_Equation3294 (G : Type*) [Magma G] (h : Equation3273 G) : Equation3294 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq37 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).2 in 16
  subsumption eq37 eq21


@[equational_result]
theorem Equation3273_implies_Equation3674 (G : Type*) [Magma G] (h : Equation3273 G) : Equation3674 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X3 ◇ (X1 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq20 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.2.2 in 9
  have eq26 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X1 ◇ X1)) := superpose eq13 eq22 -- forward demodulation 22,13
  have eq79 (X0 : G) : (X0 ◇ X0) ≠ ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).1 in 10
  subsumption eq79 eq26


@[equational_result]
theorem Equation3273_implies_Equation3678 (G : Type*) [Magma G] (h : Equation3273 G) : Equation3678 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X3 ◇ (X1 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq20 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.2.2 in 9
  have eq26 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X1 ◇ X1)) := superpose eq13 eq22 -- forward demodulation 22,13
  have eq70 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2.2 in 10
  subsumption eq70 eq26


@[equational_result]
theorem Equation3273_implies_Equation3260 (G : Type*) [Magma G] (h : Equation3273 G) : Equation3260 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq37 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).2 in 16
  subsumption eq37 eq21


@[equational_result]
theorem Equation3273_implies_Equation3295 (G : Type*) [Magma G] (h : Equation3273 G) : Equation3295 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq37 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).2 in 16
  subsumption eq37 eq21


@[equational_result]
theorem Equation3273_implies_Equation3281 (G : Type*) [Magma G] (h : Equation3273 G) : Equation3281 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq37 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).2 in 16
  subsumption eq37 eq21


@[equational_result]
theorem Equation3273_implies_Equation307 (G : Type*) [Magma G] (h : Equation3273 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.2 in 8
  have eq19 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq23 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2 in 9
  subsumption eq23 eq19


@[equational_result]
theorem Equation3273_implies_Equation3283 (G : Type*) [Magma G] (h : Equation3273 G) : Equation3283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq37 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).2 in 16
  subsumption eq37 eq21


@[equational_result]
theorem Equation3273_implies_Equation3292 (G : Type*) [Magma G] (h : Equation3273 G) : Equation3292 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq37 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).2 in 16
  subsumption eq37 eq21


@[equational_result]
theorem Equation3273_implies_Equation3664 (G : Type*) [Magma G] (h : Equation3273 G) : Equation3664 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X3 ◇ (X1 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq20 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.2.2 in 9
  have eq26 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X1 ◇ X1)) := superpose eq13 eq22 -- forward demodulation 22,13
  have eq70 (X0 : G) : (X0 ◇ X0) ≠ ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).1 in 10
  subsumption eq70 eq26


@[equational_result]
theorem Equation2787_implies_Equation2503 (G : Type*) [Magma G] (h : Equation2787 G) : Equation2503 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq29 (X0 X3 X4 : G) : ((X3 ◇ ((X0 ◇ X3) ◇ X4)) ◇ X4) = X4 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2.1 in 11
  have eq112 : sK0 ≠ sK0 := superpose eq29 eq10 -- superposition 10,29, 29 into 10, unify on (0).2 in 29 and (0).2 in 10
  subsumption eq112 rfl


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
theorem Equation2787_implies_Equation4666 (G : Type*) [Magma G] (h : Equation2787 G) : Equation4666 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq21 : sK1 ≠ ((sK2 ◇ sK1) ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
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
theorem Equation2787_implies_Equation3149 (G : Type*) [Magma G] (h : Equation2787 G) : Equation3149 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation583_implies_Equation4693 (G : Type*) [Magma G] (h : Equation583 G) : Equation4693 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK3 ◇ sK4) ◇ sK2) := mod_symm nh
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ ((X0 ◇ sK4) ◇ sK2) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation583_implies_Equation524 (G : Type*) [Magma G] (h : Equation583 G) : Equation524 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X3)) = (X4 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq25 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X2)))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq56 (X0 X1 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq56 eq25


@[equational_result]
theorem Equation209_implies_Equation1426 (G : Type*) [Magma G] (h : Equation209 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq13 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq13 rfl


@[equational_result]
theorem Equation209_implies_Equation1452 (G : Type*) [Magma G] (h : Equation209 G) : Equation1452 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq14 rfl


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
theorem Equation554_implies_Equation4146 (G : Type*) [Magma G] (h : Equation554 G) : Equation4146 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ ((X0 ◇ sK2) ◇ sK1) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.1 in 13
  subsumption eq20 eq14


@[equational_result]
theorem Equation206_implies_Equation2238 (G : Type*) [Magma G] (h : Equation206 G) : Equation2238 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1 in 10
  have eq15 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq13 eq9 -- backward demodulation 9,13
  subsumption eq15 eq8


@[equational_result]
theorem Equation206_implies_Equation3522 (G : Type*) [Magma G] (h : Equation206 G) : Equation3522 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq17 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.1 in 9
  have eq20 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- backward demodulation 10,17
  subsumption eq20 rfl


@[equational_result]
theorem Equation206_implies_Equation4065 (G : Type*) [Magma G] (h : Equation206 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1 in 10
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.1 in 8
  have eq19 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq16 eq9 -- backward demodulation 9,16
  subsumption eq19 rfl


@[equational_result]
theorem Equation206_implies_Equation1629 (G : Type*) [Magma G] (h : Equation206 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1 in 10
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.1 in 8
  have eq19 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq16 eq9 -- backward demodulation 9,16
  subsumption eq19 eq16


@[equational_result]
theorem Equation206_implies_Equation1426 (G : Type*) [Magma G] (h : Equation206 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1 in 10
  have eq15 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq13 eq9 -- backward demodulation 9,13
  have eq19 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.1.2 in 8
  have eq20 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq19 -- forward demodulation 19,13
  have eq54 : sK0 ≠ sK0 := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq54 rfl


@[equational_result]
theorem Equation206_implies_Equation4118 (G : Type*) [Magma G] (h : Equation206 G) : Equation4118 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq17 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.1 in 9
  have eq20 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- backward demodulation 10,17
  subsumption eq20 rfl


@[equational_result]
theorem Equation206_implies_Equation151 (G : Type*) [Magma G] (h : Equation206 G) : Equation151 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1 in 10
  have eq18 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.1.2 in 8
  have eq19 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq18 -- forward demodulation 18,13
  have eq38 : sK0 ≠ sK0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2 in 9
  subsumption eq38 rfl


@[equational_result]
theorem Equation206_implies_Equation3253 (G : Type*) [Magma G] (h : Equation206 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1 in 10
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq13 eq9 -- backward demodulation 9,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation206_implies_Equation3050 (G : Type*) [Magma G] (h : Equation206 G) : Equation3050 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1 in 10
  have eq15 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).1 in 10
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.1 in 8
  have eq19 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq15 eq9 -- backward demodulation 9,15
  have eq34 : sK0 ≠ sK0 := superpose eq16 eq19 -- superposition 19,16, 16 into 19, unify on (0).2 in 16 and (0).2 in 19
  subsumption eq34 rfl


@[equational_result]
theorem Equation206_implies_Equation2441 (G : Type*) [Magma G] (h : Equation206 G) : Equation2441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1 in 10
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.1 in 8
  have eq19 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq16 eq9 -- backward demodulation 9,16
  subsumption eq19 eq16


@[equational_result]
theorem Equation206_implies_Equation1832 (G : Type*) [Magma G] (h : Equation206 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1 in 10
  have eq15 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq13 eq9 -- backward demodulation 9,13
  have eq19 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.1.2 in 8
  have eq20 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq19 -- forward demodulation 19,13
  have eq54 : sK0 ≠ sK0 := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq54 rfl


@[equational_result]
theorem Equation206_implies_Equation307 (G : Type*) [Magma G] (h : Equation206 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1 in 10
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2 in 9
  subsumption eq15 rfl


@[equational_result]
theorem Equation206_implies_Equation23 (G : Type*) [Magma G] (h : Equation206 G) : Equation23 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1 in 10
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.1 in 8
  have eq22 : sK0 ≠ sK0 := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2 in 9
  subsumption eq22 rfl


@[equational_result]
theorem Equation1904_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1904 G) : Equation1223 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.2 in 8
  have eq33 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.2 in 11
  have eq38 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := superpose eq33 eq9 -- backward demodulation 9,33
  have eq39 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq33 eq38 -- forward demodulation 38,33
  subsumption eq39 eq11


@[equational_result]
theorem Equation1904_implies_Equation1701 (G : Type*) [Magma G] (h : Equation1904 G) : Equation1701 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq49 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq14 eq20 -- superposition 20,14, 14 into 20, unify on (0).2 in 14 and (0).2.2 in 20
  have eq56 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq49 eq10 -- backward demodulation 10,49
  subsumption eq56 eq14


@[equational_result]
theorem Equation1904_implies_Equation1631 (G : Type*) [Magma G] (h : Equation1904 G) : Equation1631 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq18 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = ((X4 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq95 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) := superpose eq14 eq18 -- superposition 18,14, 14 into 18, unify on (0).2 in 14 and (0).2.2 in 18
  have eq339 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X2) ◇ X1) := superpose eq9 eq95 -- superposition 95,9, 9 into 95, unify on (0).2 in 9 and (0).2.1 in 95
  have eq377 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq339 eq10 -- backward demodulation 10,339
  subsumption eq377 eq14


@[equational_result]
theorem Equation1904_implies_Equation1258 (G : Type*) [Magma G] (h : Equation1904 G) : Equation1258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq49 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq14 eq20 -- superposition 20,14, 14 into 20, unify on (0).2 in 14 and (0).2.2 in 20
  have eq56 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq49 eq10 -- backward demodulation 10,49
  subsumption eq56 eq12


@[equational_result]
theorem Equation1904_implies_Equation4090 (G : Type*) [Magma G] (h : Equation1904 G) : Equation4090 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq49 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq14 eq20 -- superposition 20,14, 14 into 20, unify on (0).2 in 14 and (0).2.2 in 20
  have eq118 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2 in 10
  subsumption eq118 rfl


@[equational_result]
theorem Equation1904_implies_Equation1958 (G : Type*) [Magma G] (h : Equation1904 G) : Equation1958 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq15 (X1 X3 X4 : G) : (X3 ◇ ((X1 ◇ X1) ◇ X4)) = (X1 ◇ ((X3 ◇ ((X1 ◇ X1) ◇ X4)) ◇ (X3 ◇ ((X1 ◇ X1) ◇ X4)))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq18 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = ((X4 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq95 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) := superpose eq14 eq18 -- superposition 18,14, 14 into 18, unify on (0).2 in 14 and (0).2.2 in 18
  have eq138 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).1.2 in 15
  have eq339 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X2) ◇ X1) := superpose eq9 eq95 -- superposition 95,9, 9 into 95, unify on (0).2 in 9 and (0).2.1 in 95
  have eq383 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq14 eq339 -- superposition 339,14, 14 into 339, unify on (0).2 in 14 and (0).2.1 in 339
  have eq453 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq383 eq138 -- backward demodulation 138,383
  have eq548 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq453 eq9 -- superposition 9,453, 453 into 9, unify on (0).2 in 453 and (0).1.1.2 in 9
  have eq804 : sK0 ≠ sK0 := superpose eq548 eq10 -- superposition 10,548, 548 into 10, unify on (0).2 in 548 and (0).2 in 10
  subsumption eq804 rfl


@[equational_result]
theorem Equation1904_implies_Equation1691 (G : Type*) [Magma G] (h : Equation1904 G) : Equation1691 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq49 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq14 eq20 -- superposition 20,14, 14 into 20, unify on (0).2 in 14 and (0).2.2 in 20
  have eq56 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq49 eq10 -- backward demodulation 10,49
  subsumption eq56 eq14


@[equational_result]
theorem Equation1904_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1904 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.2 in 8
  have eq33 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.2 in 11
  have eq38 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq33 eq9 -- backward demodulation 9,33
  subsumption eq38 eq13


@[equational_result]
theorem Equation1904_implies_Equation3887 (G : Type*) [Magma G] (h : Equation1904 G) : Equation3887 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq38 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2 in 9
  have eq266 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X2 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq20 eq38 -- superposition 38,20, 20 into 38, unify on (0).2 in 20 and (0).2.1.2 in 38
  have eq644 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq266 eq10 -- superposition 10,266, 266 into 10, unify on (0).2 in 266 and (0).2 in 10
  subsumption eq644 rfl


@[equational_result]
theorem Equation1904_implies_Equation1238 (G : Type*) [Magma G] (h : Equation1904 G) : Equation1238 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq49 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq14 eq20 -- superposition 20,14, 14 into 20, unify on (0).2 in 14 and (0).2.2 in 20
  have eq56 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq49 eq10 -- backward demodulation 10,49
  subsumption eq56 eq12


@[equational_result]
theorem Equation1904_implies_Equation1045 (G : Type*) [Magma G] (h : Equation1904 G) : Equation1045 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq38 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2 in 9
  have eq266 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X2 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq20 eq38 -- superposition 38,20, 20 into 38, unify on (0).2 in 20 and (0).2.1.2 in 38
  have eq312 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq266 eq10 -- backward demodulation 10,266
  subsumption eq312 eq12


@[equational_result]
theorem Equation1904_implies_Equation1055 (G : Type*) [Magma G] (h : Equation1904 G) : Equation1055 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq38 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2 in 9
  have eq266 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X2 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq20 eq38 -- superposition 38,20, 20 into 38, unify on (0).2 in 20 and (0).2.1.2 in 38
  have eq312 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq266 eq10 -- backward demodulation 10,266
  subsumption eq312 eq12


@[equational_result]
theorem Equation1904_implies_Equation1684 (G : Type*) [Magma G] (h : Equation1904 G) : Equation1684 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq18 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = ((X4 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq95 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) := superpose eq14 eq18 -- superposition 18,14, 14 into 18, unify on (0).2 in 14 and (0).2.2 in 18
  have eq339 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X2) ◇ X1) := superpose eq9 eq95 -- superposition 95,9, 9 into 95, unify on (0).2 in 9 and (0).2.1 in 95
  have eq377 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq339 eq10 -- backward demodulation 10,339
  subsumption eq377 eq14


@[equational_result]
theorem Equation1904_implies_Equation4080 (G : Type*) [Magma G] (h : Equation1904 G) : Equation4080 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq49 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq14 eq20 -- superposition 20,14, 14 into 20, unify on (0).2 in 14 and (0).2.2 in 20
  have eq56 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq49 eq10 -- backward demodulation 10,49
  subsumption eq56 eq49


@[equational_result]
theorem Equation1904_implies_Equation1687 (G : Type*) [Magma G] (h : Equation1904 G) : Equation1687 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq18 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = ((X4 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq95 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) := superpose eq14 eq18 -- superposition 18,14, 14 into 18, unify on (0).2 in 14 and (0).2.2 in 18
  have eq339 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X2) ◇ X1) := superpose eq9 eq95 -- superposition 95,9, 9 into 95, unify on (0).2 in 9 and (0).2.1 in 95
  have eq377 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq339 eq10 -- backward demodulation 10,339
  subsumption eq377 eq14


@[equational_result]
theorem Equation1904_implies_Equation364 (G : Type*) [Magma G] (h : Equation1904 G) : Equation364 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq49 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq14 eq20 -- superposition 20,14, 14 into 20, unify on (0).2 in 14 and (0).2.2 in 20
  have eq130 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2 in 10
  subsumption eq130 rfl


@[equational_result]
theorem Equation1904_implies_Equation1634 (G : Type*) [Magma G] (h : Equation1904 G) : Equation1634 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq49 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq14 eq20 -- superposition 20,14, 14 into 20, unify on (0).2 in 14 and (0).2.2 in 20
  have eq56 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq49 eq10 -- backward demodulation 10,49
  subsumption eq56 eq14


@[equational_result]
theorem Equation1904_implies_Equation4100 (G : Type*) [Magma G] (h : Equation1904 G) : Equation4100 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq49 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq14 eq20 -- superposition 20,14, 14 into 20, unify on (0).2 in 14 and (0).2.2 in 20
  have eq118 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2 in 10
  subsumption eq118 rfl


@[equational_result]
theorem Equation1904_implies_Equation4635 (G : Type*) [Magma G] (h : Equation1904 G) : Equation4635 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq18 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = ((X4 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq49 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq14 eq20 -- superposition 20,14, 14 into 20, unify on (0).2 in 14 and (0).2.2 in 20
  have eq56 : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq49 eq10 -- backward demodulation 10,49
  have eq81 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) := superpose eq14 eq18 -- superposition 18,14, 14 into 18, unify on (0).2 in 14 and (0).2.2 in 18
  have eq385 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X2) ◇ X1) := superpose eq9 eq81 -- superposition 81,9, 9 into 81, unify on (0).2 in 9 and (0).2.1 in 81
  have eq479 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq385 eq56 -- superposition 56,385, 385 into 56, unify on (0).2 in 385 and (0).1 in 56
  subsumption eq479 rfl


@[equational_result]
theorem Equation1904_implies_Equation3353 (G : Type*) [Magma G] (h : Equation1904 G) : Equation3353 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq15 (X1 X3 X4 : G) : (X3 ◇ ((X1 ◇ X1) ◇ X4)) = (X1 ◇ ((X3 ◇ ((X1 ◇ X1) ◇ X4)) ◇ (X3 ◇ ((X1 ◇ X1) ◇ X4)))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq18 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = ((X4 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq95 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) := superpose eq14 eq18 -- superposition 18,14, 14 into 18, unify on (0).2 in 14 and (0).2.2 in 18
  have eq138 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).1.2 in 15
  have eq339 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X2) ◇ X1) := superpose eq9 eq95 -- superposition 95,9, 9 into 95, unify on (0).2 in 9 and (0).2.1 in 95
  have eq383 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq14 eq339 -- superposition 339,14, 14 into 339, unify on (0).2 in 14 and (0).2.1 in 339
  have eq453 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq383 eq138 -- backward demodulation 138,383
  have eq556 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq453 eq10 -- superposition 10,453, 453 into 10, unify on (0).2 in 453 and (0).2 in 10
  subsumption eq556 rfl


@[equational_result]
theorem Equation1904_implies_Equation4642 (G : Type*) [Magma G] (h : Equation1904 G) : Equation4642 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK2 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq18 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = ((X4 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq49 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq14 eq20 -- superposition 20,14, 14 into 20, unify on (0).2 in 14 and (0).2.2 in 20
  have eq56 : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq49 eq10 -- backward demodulation 10,49
  have eq81 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) := superpose eq14 eq18 -- superposition 18,14, 14 into 18, unify on (0).2 in 14 and (0).2.2 in 18
  have eq385 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X2) ◇ X1) := superpose eq9 eq81 -- superposition 81,9, 9 into 81, unify on (0).2 in 9 and (0).2.1 in 81
  have eq479 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq385 eq56 -- superposition 56,385, 385 into 56, unify on (0).2 in 385 and (0).1 in 56
  subsumption eq479 rfl


@[equational_result]
theorem Equation1904_implies_Equation3897 (G : Type*) [Magma G] (h : Equation1904 G) : Equation3897 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq38 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2 in 9
  have eq266 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X2 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq20 eq38 -- superposition 38,20, 20 into 38, unify on (0).2 in 20 and (0).2.1.2 in 38
  have eq644 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq266 eq10 -- superposition 10,266, 266 into 10, unify on (0).2 in 266 and (0).2 in 10
  subsumption eq644 rfl


@[equational_result]
theorem Equation4088_implies_Equation3685 (G : Type*) [Magma G] (h : Equation4088 G) : Equation3685 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq13 (X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq14 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq43 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq64 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X0) := superpose eq14 eq43 -- superposition 43,14, 14 into 43, unify on (0).2 in 14 and (0).1 in 43
  have eq79 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (sK0 ◇ sK1)) := superpose eq43 eq10 -- superposition 10,43, 43 into 10, unify on (0).2 in 43 and (0).2.1 in 10
  subsumption eq79 eq64


@[equational_result]
theorem Equation4088_implies_Equation4110 (G : Type*) [Magma G] (h : Equation4088 G) : Equation4110 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq14 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq28 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.1 in 9
  have eq37 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq28 -- superposition 28,9, 9 into 28, unify on (0).2 in 9 and (0).2 in 28
  have eq115 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq37 eq16 -- superposition 16,37, 37 into 16, unify on (0).2 in 37 and (0).2 in 16
  subsumption eq115 eq37


@[equational_result]
theorem Equation4088_implies_Equation4078 (G : Type*) [Magma G] (h : Equation4088 G) : Equation4078 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq14 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.1 in 9
  have eq37 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq27 -- superposition 27,9, 9 into 27, unify on (0).2 in 9 and (0).2 in 27
  have eq115 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq37 eq16 -- superposition 16,37, 37 into 16, unify on (0).2 in 37 and (0).2 in 16
  subsumption eq115 eq37


@[equational_result]
theorem Equation4088_implies_Equation3665 (G : Type*) [Magma G] (h : Equation4088 G) : Equation3665 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq13 (X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq43 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq71 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq43 eq10 -- superposition 10,43, 43 into 10, unify on (0).2 in 43 and (0).2 in 10
  subsumption eq71 eq43


@[equational_result]
theorem Equation4088_implies_Equation4070 (G : Type*) [Magma G] (h : Equation4088 G) : Equation4070 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq14 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.1 in 9
  have eq37 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq27 -- superposition 27,9, 9 into 27, unify on (0).2 in 9 and (0).2 in 27
  have eq115 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq37 eq16 -- superposition 16,37, 37 into 16, unify on (0).2 in 37 and (0).2 in 16
  subsumption eq115 eq37


@[equational_result]
theorem Equation4088_implies_Equation40 (G : Type*) [Magma G] (h : Equation4088 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq13 (X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq42 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq70 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq42 eq10 -- superposition 10,42, 42 into 10, unify on (0).2 in 42 and (0).2 in 10
  subsumption eq70 eq42


@[equational_result]
theorem Equation4088_implies_Equation4093 (G : Type*) [Magma G] (h : Equation4088 G) : Equation4093 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq14 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation4088_implies_Equation4115 (G : Type*) [Magma G] (h : Equation4088 G) : Equation4115 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK3) ◇ sK3) := mod_symm nh
  have eq14 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.1 in 9
  have eq37 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq27 -- superposition 27,9, 9 into 27, unify on (0).2 in 9 and (0).2 in 27
  have eq115 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq37 eq16 -- superposition 16,37, 37 into 16, unify on (0).2 in 37 and (0).2 in 16
  subsumption eq115 eq37


@[equational_result]
theorem Equation4088_implies_Equation4608 (G : Type*) [Magma G] (h : Equation4088 G) : Equation4608 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq14 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq44 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq65 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = (X2 ◇ X2) := superpose eq14 eq44 -- superposition 44,14, 14 into 44, unify on (0).2 in 14 and (0).1 in 44
  have eq80 (X0 : G) : (X0 ◇ X0) ≠ ((X0 ◇ X0) ◇ sK1) := superpose eq44 eq17 -- superposition 17,44, 44 into 17, unify on (0).2 in 44 and (0).1 in 17
  subsumption eq80 eq65


@[equational_result]
theorem Equation3051_implies_Equation3258 (G : Type*) [Magma G] (h : Equation3051 G) : Equation3258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq13 (X0 X1 : G) : (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)))) ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1.1 in 11
  have eq18 (X0 X1 : G) : (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = (X0 ◇ X1) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq19 (X0 X1 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = (X0 ◇ X1) := superpose eq11 eq18 -- forward demodulation 18,11
  have eq20 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = (X0 ◇ X1) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq32 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq20 eq20 -- superposition 20,20, 20 into 20, unify on (0).2 in 20 and (0).1 in 20
  have eq72 (X0 : G) : (sK0 ◇ X0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ X0))) := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).1 in 10
  subsumption eq72 eq32


@[equational_result]
theorem Equation3051_implies_Equation3463 (G : Type*) [Magma G] (h : Equation3051 G) : Equation3463 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq13 (X0 X1 : G) : (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)))) ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1.1 in 11
  have eq18 (X0 X1 : G) : (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = (X0 ◇ X1) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq19 (X0 X1 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = (X0 ◇ X1) := superpose eq11 eq18 -- forward demodulation 18,11
  have eq20 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = (X0 ◇ X1) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq32 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq20 eq20 -- superposition 20,20, 20 into 20, unify on (0).2 in 20 and (0).1 in 20
  have eq72 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2.2 in 10
  subsumption eq72 eq32


