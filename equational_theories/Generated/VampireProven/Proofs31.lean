import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation1465_implies_Equation1437 (G : Type*) [Magma G] (h : Equation1465 G) : Equation1437 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq47 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation1465_implies_Equation1473 (G : Type*) [Magma G] (h : Equation1465 G) : Equation1473 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq47 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation2420_implies_Equation2533 (G : Type*) [Magma G] (h : Equation2420 G) : Equation2533 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X3)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2420_implies_Equation2310 (G : Type*) [Magma G] (h : Equation2420 G) : Equation2310 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X3)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq70 : sK0 ≠ sK0 := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq70 rfl


@[equational_result]
theorem Equation2420_implies_Equation2659 (G : Type*) [Magma G] (h : Equation2420 G) : Equation2659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X3)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq14 (X3 X4 : G) : ((X3 ◇ X3) ◇ X4) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X2) = X2 := superpose eq14 eq11 -- superposition 11,14, 14 into 11, unify on (0).2 in 14 and (0).1.1 in 11
  have eq93 : sK0 ≠ sK0 := superpose eq54 eq10 -- superposition 10,54, 54 into 10, unify on (0).2 in 54 and (0).2 in 10
  subsumption eq93 rfl


@[equational_result]
theorem Equation2420_implies_Equation2791 (G : Type*) [Magma G] (h : Equation2420 G) : Equation2791 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X3)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq14 (X3 X4 : G) : ((X3 ◇ X3) ◇ X4) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X2) = X2 := superpose eq14 eq11 -- superposition 11,14, 14 into 11, unify on (0).2 in 14 and (0).1.1 in 11
  have eq93 : sK0 ≠ sK0 := superpose eq54 eq10 -- superposition 10,54, 54 into 10, unify on (0).2 in 54 and (0).2 in 10
  subsumption eq93 rfl


@[equational_result]
theorem Equation2420_implies_Equation242 (G : Type*) [Magma G] (h : Equation2420 G) : Equation242 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X3)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation765_implies_Equation4073 (G : Type*) [Magma G] (h : Equation765 G) : Equation4073 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X2 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq36 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = X2 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.2 in 11
  have eq142 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).1.2 in 36
  have eq1096 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq142 eq10 -- superposition 10,142, 142 into 10, unify on (0).2 in 142 and (0).2 in 10
  subsumption eq1096 rfl


@[equational_result]
theorem Equation765_implies_Equation4320 (G : Type*) [Magma G] (h : Equation765 G) : Equation4320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X2 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq36 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = X2 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.2 in 11
  have eq69 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) = X2 := superpose eq13 eq18 -- superposition 18,13, 13 into 18, unify on (0).2 in 13 and (0).1.2 in 18
  have eq141 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) = X2 := superpose eq13 eq36 -- superposition 36,13, 13 into 36, unify on (0).2 in 13 and (0).1.2 in 36
  have eq795 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq69 eq141 -- superposition 141,69, 69 into 141, unify on (0).2 in 69 and (0).1.2.2 in 141
  have eq5051 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq795 eq10 -- superposition 10,795, 795 into 10, unify on (0).2 in 795 and (0).2 in 10
  subsumption eq5051 rfl


@[equational_result]
theorem Equation765_implies_Equation842 (G : Type*) [Magma G] (h : Equation765 G) : Equation842 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X2 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1.2 in 13
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq36 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = X2 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.2 in 11
  have eq69 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) = X2 := superpose eq13 eq18 -- superposition 18,13, 13 into 18, unify on (0).2 in 13 and (0).1.2 in 18
  have eq84 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X5)) = (X4 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X5)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.1 in 12
  have eq100 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X1 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.1 in 13
  have eq107 (X0 X1 X2 X3 X5 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X5)) = (X1 ◇ ((X2 ◇ X3) ◇ X5)) := superpose eq12 eq84 -- forward demodulation 84,12
  have eq116 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X5)) = (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X5)) := superpose eq100 eq107 -- backward demodulation 107,100
  have eq122 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X5)) = (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X5)) := superpose eq100 eq116 -- forward demodulation 116,100
  have eq141 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) = X2 := superpose eq13 eq36 -- superposition 36,13, 13 into 36, unify on (0).2 in 13 and (0).1.2 in 36
  have eq233 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X3) := superpose eq69 eq13 -- superposition 13,69, 69 into 13, unify on (0).2 in 69 and (0).2.1.2 in 13
  have eq257 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X4) = (((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ X4) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2.1.1.2 in 14
  have eq287 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ ((X3 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2)) ◇ X4))) = X4 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2 in 9
  have eq304 (X0 X1 X2 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X4) = ((X2 ◇ X1) ◇ X4) := superpose eq233 eq257 -- forward demodulation 257,233
  have eq350 (X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X4))) = X4 := superpose eq304 eq287 -- forward demodulation 287,304
  have eq351 (X2 X3 X4 : G) : (X3 ◇ (X3 ◇ ((X2 ◇ X2) ◇ X4))) = X4 := superpose eq122 eq350 -- forward demodulation 350,122
  have eq795 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq69 eq141 -- superposition 141,69, 69 into 141, unify on (0).2 in 69 and (0).1.2.2 in 141
  have eq872 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0))) := superpose eq795 eq10 -- backward demodulation 10,795
  subsumption eq872 eq351


@[equational_result]
theorem Equation765_implies_Equation4146 (G : Type*) [Magma G] (h : Equation765 G) : Equation4146 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X2 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq36 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = X2 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.2 in 11
  have eq142 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).1.2 in 36
  have eq1096 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq142 eq10 -- superposition 10,142, 142 into 10, unify on (0).2 in 142 and (0).2 in 10
  subsumption eq1096 rfl


@[equational_result]
theorem Equation765_implies_Equation872 (G : Type*) [Magma G] (h : Equation765 G) : Equation872 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X2 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1.2 in 13
  have eq19 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq36 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = X2 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.2 in 11
  have eq69 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) = X2 := superpose eq13 eq19 -- superposition 19,13, 13 into 19, unify on (0).2 in 13 and (0).1.2 in 19
  have eq84 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X5)) = (X4 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X5)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.1 in 12
  have eq100 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X1 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.1 in 13
  have eq107 (X0 X1 X2 X3 X5 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X5)) = (X1 ◇ ((X2 ◇ X3) ◇ X5)) := superpose eq12 eq84 -- forward demodulation 84,12
  have eq116 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X5)) = (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X5)) := superpose eq100 eq107 -- backward demodulation 107,100
  have eq122 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X5)) = (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X5)) := superpose eq100 eq116 -- forward demodulation 116,100
  have eq141 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) = X2 := superpose eq13 eq36 -- superposition 36,13, 13 into 36, unify on (0).2 in 13 and (0).1.2 in 36
  have eq231 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X3) := superpose eq69 eq13 -- superposition 13,69, 69 into 13, unify on (0).2 in 69 and (0).2.1.2 in 13
  have eq257 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X4) = (((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ X4) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2.1.1.2 in 14
  have eq287 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ ((X3 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2)) ◇ X4))) = X4 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2 in 9
  have eq304 (X0 X1 X2 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X4) = ((X2 ◇ X1) ◇ X4) := superpose eq231 eq257 -- forward demodulation 257,231
  have eq350 (X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X4))) = X4 := superpose eq304 eq287 -- forward demodulation 287,304
  have eq351 (X2 X3 X4 : G) : (X3 ◇ (X3 ◇ ((X2 ◇ X2) ◇ X4))) = X4 := superpose eq122 eq350 -- forward demodulation 350,122
  have eq795 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq69 eq141 -- superposition 141,69, 69 into 141, unify on (0).2 in 69 and (0).1.2.2 in 141
  have eq872 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0))) := superpose eq795 eq10 -- backward demodulation 10,795
  subsumption eq872 eq351


@[equational_result]
theorem Equation765_implies_Equation3887 (G : Type*) [Magma G] (h : Equation765 G) : Equation3887 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq76 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq18 eq13 -- superposition 13,18, 18 into 13, unify on (0).2 in 18 and (0).2.1 in 13
  have eq561 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq76 eq10 -- superposition 10,76, 76 into 10, unify on (0).2 in 76 and (0).2 in 10
  subsumption eq561 rfl


@[equational_result]
theorem Equation765_implies_Equation4165 (G : Type*) [Magma G] (h : Equation765 G) : Equation4165 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq76 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq18 eq13 -- superposition 13,18, 18 into 13, unify on (0).2 in 18 and (0).2.1 in 13
  have eq104 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X1 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.1 in 13
  have eq1200 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) := superpose eq104 eq10 -- superposition 10,104, 104 into 10, unify on (0).2 in 104 and (0).2 in 10
  subsumption eq1200 eq76


@[equational_result]
theorem Equation765_implies_Equation4023 (G : Type*) [Magma G] (h : Equation765 G) : Equation4023 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq76 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq18 eq13 -- superposition 13,18, 18 into 13, unify on (0).2 in 18 and (0).2.1 in 13
  have eq561 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq76 eq10 -- superposition 10,76, 76 into 10, unify on (0).2 in 76 and (0).2 in 10
  subsumption eq561 rfl


@[equational_result]
theorem Equation765_implies_Equation4362 (G : Type*) [Magma G] (h : Equation765 G) : Equation4362 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X2 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq36 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = X2 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.2 in 11
  have eq69 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) = X2 := superpose eq13 eq18 -- superposition 18,13, 13 into 18, unify on (0).2 in 13 and (0).1.2 in 18
  have eq141 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) = X2 := superpose eq13 eq36 -- superposition 36,13, 13 into 36, unify on (0).2 in 13 and (0).1.2 in 36
  have eq795 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq69 eq141 -- superposition 141,69, 69 into 141, unify on (0).2 in 69 and (0).1.2.2 in 141
  have eq5051 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq795 eq10 -- superposition 10,795, 795 into 10, unify on (0).2 in 795 and (0).2 in 10
  subsumption eq5051 rfl


@[equational_result]
theorem Equation765_implies_Equation1515 (G : Type*) [Magma G] (h : Equation765 G) : Equation1515 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1.2 in 13
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq20 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3))) = X3 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq69 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) = X2 := superpose eq13 eq18 -- superposition 18,13, 13 into 18, unify on (0).2 in 13 and (0).1.2 in 18
  have eq72 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq18 eq13 -- superposition 13,18, 18 into 13, unify on (0).2 in 18 and (0).2.1 in 13
  have eq84 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X5)) = (X4 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X5)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.1 in 12
  have eq100 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X1 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.1 in 13
  have eq107 (X0 X1 X2 X3 X5 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X5)) = (X1 ◇ ((X2 ◇ X3) ◇ X5)) := superpose eq12 eq84 -- forward demodulation 84,12
  have eq116 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X5)) = (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X5)) := superpose eq100 eq107 -- backward demodulation 107,100
  have eq117 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X3)) = (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) := superpose eq100 eq12 -- backward demodulation 12,100
  have eq122 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X5)) = (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X5)) := superpose eq100 eq116 -- forward demodulation 116,100
  have eq185 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) := superpose eq117 eq9 -- superposition 9,117, 117 into 9, unify on (0).2 in 117 and (0).1.2.2 in 9
  have eq200 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3)))))) = X3 := superpose eq185 eq20 -- backward demodulation 20,185
  have eq233 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X3) := superpose eq69 eq13 -- superposition 13,69, 69 into 13, unify on (0).2 in 69 and (0).2.1.2 in 13
  have eq257 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X4) = (((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ X4) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2.1.1.2 in 14
  have eq287 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ ((X3 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2)) ◇ X4))) = X4 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2 in 9
  have eq304 (X0 X1 X2 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X4) = ((X2 ◇ X1) ◇ X4) := superpose eq233 eq257 -- forward demodulation 257,233
  have eq350 (X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X4))) = X4 := superpose eq304 eq287 -- forward demodulation 287,304
  have eq351 (X2 X3 X4 : G) : (X3 ◇ (X3 ◇ ((X2 ◇ X2) ◇ X4))) = X4 := superpose eq122 eq350 -- forward demodulation 350,122
  have eq559 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq72 eq117 -- superposition 117,72, 72 into 117, unify on (0).2 in 72 and (0).2.2 in 117
  have eq2109 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ (X2 ◇ X1))) = X1 := superpose eq351 eq200 -- superposition 200,351, 351 into 200, unify on (0).2 in 351 and (0).1.2.2.2 in 200
  have eq4083 (X0 : G) : sK0 ≠ ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ sK0))) := superpose eq559 eq10 -- superposition 10,559, 559 into 10, unify on (0).2 in 559 and (0).2.2 in 10
  subsumption eq4083 eq2109


@[equational_result]
theorem Equation765_implies_Equation4090 (G : Type*) [Magma G] (h : Equation765 G) : Equation4090 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq76 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq18 eq13 -- superposition 13,18, 18 into 13, unify on (0).2 in 18 and (0).2.1 in 13
  have eq104 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X1 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.1 in 13
  have eq1200 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq104 eq10 -- superposition 10,104, 104 into 10, unify on (0).2 in 104 and (0).2 in 10
  subsumption eq1200 eq76


@[equational_result]
theorem Equation765_implies_Equation703 (G : Type*) [Magma G] (h : Equation765 G) : Equation703 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1.2 in 13
  have eq19 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq69 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) = X2 := superpose eq13 eq19 -- superposition 19,13, 13 into 19, unify on (0).2 in 13 and (0).1.2 in 19
  have eq84 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X5)) = (X4 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X5)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.1 in 12
  have eq100 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X1 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.1 in 13
  have eq107 (X0 X1 X2 X3 X5 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X5)) = (X1 ◇ ((X2 ◇ X3) ◇ X5)) := superpose eq12 eq84 -- forward demodulation 84,12
  have eq116 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X5)) = (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X5)) := superpose eq100 eq107 -- backward demodulation 107,100
  have eq122 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X5)) = (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X5)) := superpose eq100 eq116 -- forward demodulation 116,100
  have eq231 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X3) := superpose eq69 eq13 -- superposition 13,69, 69 into 13, unify on (0).2 in 69 and (0).2.1.2 in 13
  have eq257 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X4) = (((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ X4) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2.1.1.2 in 14
  have eq287 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ ((X3 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2)) ◇ X4))) = X4 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2 in 9
  have eq304 (X0 X1 X2 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X4) = ((X2 ◇ X1) ◇ X4) := superpose eq231 eq257 -- forward demodulation 257,231
  have eq350 (X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X4))) = X4 := superpose eq304 eq287 -- forward demodulation 287,304
  have eq351 (X2 X3 X4 : G) : (X3 ◇ (X3 ◇ ((X2 ◇ X2) ◇ X4))) = X4 := superpose eq122 eq350 -- forward demodulation 350,122
  have eq1462 : sK0 ≠ sK0 := superpose eq351 eq10 -- superposition 10,351, 351 into 10, unify on (0).2 in 351 and (0).2 in 10
  subsumption eq1462 rfl


@[equational_result]
theorem Equation765_implies_Equation622 (G : Type*) [Magma G] (h : Equation765 G) : Equation622 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1.2 in 13
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq69 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) = X2 := superpose eq13 eq18 -- superposition 18,13, 13 into 18, unify on (0).2 in 13 and (0).1.2 in 18
  have eq84 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X5)) = (X4 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X5)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.1 in 12
  have eq100 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X1 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.1 in 13
  have eq107 (X0 X1 X2 X3 X5 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X5)) = (X1 ◇ ((X2 ◇ X3) ◇ X5)) := superpose eq12 eq84 -- forward demodulation 84,12
  have eq116 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X5)) = (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X5)) := superpose eq100 eq107 -- backward demodulation 107,100
  have eq122 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X5)) = (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X5)) := superpose eq100 eq116 -- forward demodulation 116,100
  have eq233 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X3) := superpose eq69 eq13 -- superposition 13,69, 69 into 13, unify on (0).2 in 69 and (0).2.1.2 in 13
  have eq257 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X4) = (((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ X4) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2.1.1.2 in 14
  have eq287 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ ((X3 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2)) ◇ X4))) = X4 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2 in 9
  have eq304 (X0 X1 X2 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X4) = ((X2 ◇ X1) ◇ X4) := superpose eq233 eq257 -- forward demodulation 257,233
  have eq350 (X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X4))) = X4 := superpose eq304 eq287 -- forward demodulation 287,304
  have eq351 (X2 X3 X4 : G) : (X3 ◇ (X3 ◇ ((X2 ◇ X2) ◇ X4))) = X4 := superpose eq122 eq350 -- forward demodulation 350,122
  have eq1505 : sK0 ≠ sK0 := superpose eq351 eq10 -- superposition 10,351, 351 into 10, unify on (0).2 in 351 and (0).2 in 10
  subsumption eq1505 rfl


@[equational_result]
theorem Equation765_implies_Equation4226 (G : Type*) [Magma G] (h : Equation765 G) : Equation4226 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK2) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq76 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq18 eq13 -- superposition 13,18, 18 into 13, unify on (0).2 in 18 and (0).2.1 in 13
  have eq104 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X1 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.1 in 13
  have eq1200 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK1) := superpose eq104 eq10 -- superposition 10,104, 104 into 10, unify on (0).2 in 104 and (0).2 in 10
  subsumption eq1200 eq76


@[equational_result]
theorem Equation765_implies_Equation731 (G : Type*) [Magma G] (h : Equation765 G) : Equation731 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK2 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1.2 in 13
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq69 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) = X2 := superpose eq13 eq18 -- superposition 18,13, 13 into 18, unify on (0).2 in 13 and (0).1.2 in 18
  have eq84 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X5)) = (X4 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X5)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.1 in 12
  have eq100 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X1 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.1 in 13
  have eq107 (X0 X1 X2 X3 X5 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X5)) = (X1 ◇ ((X2 ◇ X3) ◇ X5)) := superpose eq12 eq84 -- forward demodulation 84,12
  have eq116 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X5)) = (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X5)) := superpose eq100 eq107 -- backward demodulation 107,100
  have eq122 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X5)) = (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X5)) := superpose eq100 eq116 -- forward demodulation 116,100
  have eq233 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X3) := superpose eq69 eq13 -- superposition 13,69, 69 into 13, unify on (0).2 in 69 and (0).2.1.2 in 13
  have eq257 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X4) = (((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ X4) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2.1.1.2 in 14
  have eq287 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ ((X3 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2)) ◇ X4))) = X4 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2 in 9
  have eq304 (X0 X1 X2 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X4) = ((X2 ◇ X1) ◇ X4) := superpose eq233 eq257 -- forward demodulation 257,233
  have eq350 (X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X4))) = X4 := superpose eq304 eq287 -- forward demodulation 287,304
  have eq351 (X2 X3 X4 : G) : (X3 ◇ (X3 ◇ ((X2 ◇ X2) ◇ X4))) = X4 := superpose eq122 eq350 -- forward demodulation 350,122
  have eq1505 : sK0 ≠ sK0 := superpose eq351 eq10 -- superposition 10,351, 351 into 10, unify on (0).2 in 351 and (0).2 in 10
  subsumption eq1505 rfl


@[equational_result]
theorem Equation3061_implies_Equation3093 (G : Type*) [Magma G] (h : Equation3061 G) : Equation3093 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X3) = (((X0 ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1 in 11
  have eq37 (X0 X2 X3 : G) : ((((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) ◇ X0) = X0 := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).1.1 in 9
  have eq76 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq37 eq9 -- superposition 9,37, 37 into 9, unify on (0).2 in 37 and (0).1.1.1 in 9
  have eq221 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) = X0 := superpose eq76 eq37 -- superposition 37,76, 76 into 37, unify on (0).2 in 76 and (0).1.1 in 37
  have eq326 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = X0 := superpose eq221 eq11 -- superposition 11,221, 221 into 11, unify on (0).2 in 221 and (0).1 in 11
  have eq492 : sK0 ≠ sK0 := superpose eq326 eq10 -- superposition 10,326, 326 into 10, unify on (0).2 in 326 and (0).2 in 10
  subsumption eq492 rfl


@[equational_result]
theorem Equation3061_implies_Equation3075 (G : Type*) [Magma G] (h : Equation3061 G) : Equation3075 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X3) = (((X0 ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1 in 11
  have eq38 (X0 X2 X3 : G) : ((((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) ◇ X0) = X0 := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).1.1 in 9
  have eq76 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq38 eq9 -- superposition 9,38, 38 into 9, unify on (0).2 in 38 and (0).1.1.1 in 9
  have eq226 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) = X0 := superpose eq76 eq38 -- superposition 38,76, 76 into 38, unify on (0).2 in 76 and (0).1.1 in 38
  have eq326 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = X0 := superpose eq226 eq11 -- superposition 11,226, 226 into 11, unify on (0).2 in 226 and (0).1 in 11
  have eq501 : sK0 ≠ sK0 := superpose eq326 eq10 -- superposition 10,326, 326 into 10, unify on (0).2 in 326 and (0).2 in 10
  subsumption eq501 rfl


@[equational_result]
theorem Equation3061_implies_Equation3085 (G : Type*) [Magma G] (h : Equation3061 G) : Equation3085 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X3) = (((X0 ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1 in 11
  have eq37 (X0 X2 X3 : G) : ((((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) ◇ X0) = X0 := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).1.1 in 9
  have eq76 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq37 eq9 -- superposition 9,37, 37 into 9, unify on (0).2 in 37 and (0).1.1.1 in 9
  have eq221 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) = X0 := superpose eq76 eq37 -- superposition 37,76, 76 into 37, unify on (0).2 in 76 and (0).1.1 in 37
  have eq326 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = X0 := superpose eq221 eq11 -- superposition 11,221, 221 into 11, unify on (0).2 in 221 and (0).1 in 11
  have eq492 : sK0 ≠ sK0 := superpose eq326 eq10 -- superposition 10,326, 326 into 10, unify on (0).2 in 326 and (0).2 in 10
  subsumption eq492 rfl


@[equational_result]
theorem Equation3061_implies_Equation3089 (G : Type*) [Magma G] (h : Equation3061 G) : Equation3089 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X3) = (((X0 ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1 in 11
  have eq37 (X0 X2 X3 : G) : ((((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) ◇ X0) = X0 := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).1.1 in 9
  have eq76 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq37 eq9 -- superposition 9,37, 37 into 9, unify on (0).2 in 37 and (0).1.1.1 in 9
  have eq221 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) = X0 := superpose eq76 eq37 -- superposition 37,76, 76 into 37, unify on (0).2 in 76 and (0).1.1 in 37
  have eq326 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = X0 := superpose eq221 eq11 -- superposition 11,221, 221 into 11, unify on (0).2 in 221 and (0).1 in 11
  have eq492 : sK0 ≠ sK0 := superpose eq326 eq10 -- superposition 10,326, 326 into 10, unify on (0).2 in 326 and (0).2 in 10
  subsumption eq492 rfl


@[equational_result]
theorem Equation3061_implies_Equation3097 (G : Type*) [Magma G] (h : Equation3061 G) : Equation3097 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK3) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X3) = (((X0 ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1 in 11
  have eq37 (X0 X2 X3 : G) : ((((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) ◇ X0) = X0 := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).1.1 in 9
  have eq76 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq37 eq9 -- superposition 9,37, 37 into 9, unify on (0).2 in 37 and (0).1.1.1 in 9
  have eq221 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) = X0 := superpose eq76 eq37 -- superposition 37,76, 76 into 37, unify on (0).2 in 76 and (0).1.1 in 37
  have eq326 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = X0 := superpose eq221 eq11 -- superposition 11,221, 221 into 11, unify on (0).2 in 221 and (0).1 in 11
  have eq492 : sK0 ≠ sK0 := superpose eq326 eq10 -- superposition 10,326, 326 into 10, unify on (0).2 in 326 and (0).2 in 10
  subsumption eq492 rfl


@[equational_result]
theorem Equation2571_implies_Equation2696 (G : Type*) [Magma G] (h : Equation2571 G) : Equation2696 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq23 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq80 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq80 rfl


@[equational_result]
theorem Equation2571_implies_Equation3522 (G : Type*) [Magma G] (h : Equation2571 G) : Equation3522 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq21 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1 in 12
  have eq48 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq21 -- superposition 21,16, 16 into 21, unify on (0).2 in 16 and (0).1.1 in 21
  have eq55 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq48 eq10 -- backward demodulation 10,48
  subsumption eq55 rfl


@[equational_result]
theorem Equation2571_implies_Equation3659 (G : Type*) [Magma G] (h : Equation2571 G) : Equation3659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1.2 in 8
  have eq32 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2 in 9
  subsumption eq32 rfl


@[equational_result]
theorem Equation2571_implies_Equation4226 (G : Type*) [Magma G] (h : Equation2571 G) : Equation4226 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK2) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq125 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.1 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.1.1 in 20
  have eq185 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq148 -- superposition 148,15, 15 into 148, unify on (0).2 in 15 and (0).2.1 in 148
  have eq523 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq185 eq11 -- superposition 11,185, 185 into 11, unify on (0).2 in 185 and (0).1.1 in 11
  have eq610 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq523 eq12 -- superposition 12,523, 523 into 12, unify on (0).2 in 523 and (0).1 in 12
  have eq634 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq148 eq610 -- forward demodulation 610,148
  have eq635 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq634 eq10 -- backward demodulation 10,634
  subsumption eq635 rfl


@[equational_result]
theorem Equation2571_implies_Equation3712 (G : Type*) [Magma G] (h : Equation2571 G) : Equation3712 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq33 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq33 rfl


@[equational_result]
theorem Equation2571_implies_Equation2543 (G : Type*) [Magma G] (h : Equation2571 G) : Equation2543 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq21 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1 in 12
  have eq24 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq48 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq21 -- superposition 21,16, 16 into 21, unify on (0).2 in 16 and (0).1.1 in 21
  have eq55 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq48 eq10 -- backward demodulation 10,48
  have eq159 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq24 eq12 -- superposition 12,24, 24 into 12, unify on (0).2 in 24 and (0).1 in 12
  have eq161 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq16 eq159 -- forward demodulation 159,16
  have eq230 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq16 eq161 -- superposition 161,16, 16 into 161, unify on (0).2 in 16 and (0).2.1 in 161
  have eq565 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq230 eq11 -- superposition 11,230, 230 into 11, unify on (0).2 in 230 and (0).1.1 in 11
  have eq719 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq565 eq12 -- superposition 12,565, 565 into 12, unify on (0).2 in 565 and (0).1 in 12
  have eq728 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq161 eq719 -- forward demodulation 719,161
  have eq864 : sK0 ≠ sK0 := superpose eq728 eq55 -- superposition 55,728, 728 into 55, unify on (0).2 in 728 and (0).2 in 55
  subsumption eq864 rfl


@[equational_result]
theorem Equation2571_implies_Equation3684 (G : Type*) [Magma G] (h : Equation2571 G) : Equation3684 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq125 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.1 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.1.1 in 20
  have eq185 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq148 -- superposition 148,15, 15 into 148, unify on (0).2 in 15 and (0).2.1 in 148
  have eq523 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq185 eq11 -- superposition 11,185, 185 into 11, unify on (0).2 in 185 and (0).1.1 in 11
  have eq610 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq523 eq12 -- superposition 12,523, 523 into 12, unify on (0).2 in 523 and (0).1 in 12
  have eq634 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq148 eq610 -- forward demodulation 610,148
  have eq714 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq634 eq10 -- superposition 10,634, 634 into 10, unify on (0).2 in 634 and (0).2 in 10
  subsumption eq714 rfl


@[equational_result]
theorem Equation2571_implies_Equation4622 (G : Type*) [Magma G] (h : Equation2571 G) : Equation4622 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq125 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.1 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.1.1 in 20
  have eq185 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq148 -- superposition 148,15, 15 into 148, unify on (0).2 in 15 and (0).2.1 in 148
  have eq523 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq185 eq11 -- superposition 11,185, 185 into 11, unify on (0).2 in 185 and (0).1.1 in 11
  have eq610 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq523 eq12 -- superposition 12,523, 523 into 12, unify on (0).2 in 523 and (0).1 in 12
  have eq634 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq148 eq610 -- forward demodulation 610,148
  have eq635 : sK1 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq634 eq10 -- backward demodulation 10,634
  subsumption eq635 eq634


@[equational_result]
theorem Equation2571_implies_Equation3050 (G : Type*) [Magma G] (h : Equation2571 G) : Equation3050 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1.2 in 8
  have eq20 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).1 in 11
  have eq47 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.1 in 20
  have eq54 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq47 eq9 -- backward demodulation 9,47
  subsumption eq54 eq47


@[equational_result]
theorem Equation2571_implies_Equation2709 (G : Type*) [Magma G] (h : Equation2571 G) : Equation2709 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
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
theorem Equation2571_implies_Equation3139 (G : Type*) [Magma G] (h : Equation2571 G) : Equation3139 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq21 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1 in 12
  have eq48 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq15 eq21 -- superposition 21,15, 15 into 21, unify on (0).2 in 15 and (0).1.1 in 21
  have eq125 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.1 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.1.1 in 20
  have eq185 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq148 -- superposition 148,15, 15 into 148, unify on (0).2 in 15 and (0).2.1 in 148
  have eq523 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq185 eq11 -- superposition 11,185, 185 into 11, unify on (0).2 in 185 and (0).1.1 in 11
  have eq610 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq523 eq12 -- superposition 12,523, 523 into 12, unify on (0).2 in 523 and (0).1 in 12
  have eq634 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq148 eq610 -- forward demodulation 610,148
  have eq635 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq634 eq10 -- backward demodulation 10,634
  subsumption eq635 eq48


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
theorem Equation2571_implies_Equation4165 (G : Type*) [Magma G] (h : Equation2571 G) : Equation4165 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq125 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.1 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.1.1 in 20
  have eq185 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq148 -- superposition 148,15, 15 into 148, unify on (0).2 in 15 and (0).2.1 in 148
  have eq523 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq185 eq11 -- superposition 11,185, 185 into 11, unify on (0).2 in 185 and (0).1.1 in 11
  have eq610 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq523 eq12 -- superposition 12,523, 523 into 12, unify on (0).2 in 523 and (0).1 in 12
  have eq634 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq148 eq610 -- forward demodulation 610,148
  have eq635 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq634 eq10 -- backward demodulation 10,634
  subsumption eq635 rfl


@[equational_result]
theorem Equation2571_implies_Equation3759 (G : Type*) [Magma G] (h : Equation2571 G) : Equation3759 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq125 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq16 eq20 -- superposition 20,16, 16 into 20, unify on (0).2 in 16 and (0).1.1 in 20
  have eq156 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.1.1 in 20
  have eq204 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq156 eq10 -- superposition 10,156, 156 into 10, unify on (0).2 in 156 and (0).2 in 10
  subsumption eq204 rfl


@[equational_result]
theorem Equation2571_implies_Equation3509 (G : Type*) [Magma G] (h : Equation2571 G) : Equation3509 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq125 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.1 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.1.1 in 20
  have eq185 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq148 -- superposition 148,15, 15 into 148, unify on (0).2 in 15 and (0).2.1 in 148
  have eq523 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq185 eq11 -- superposition 11,185, 185 into 11, unify on (0).2 in 185 and (0).1.1 in 11
  have eq610 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq523 eq12 -- superposition 12,523, 523 into 12, unify on (0).2 in 523 and (0).1 in 12
  have eq634 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq148 eq610 -- forward demodulation 610,148
  have eq635 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq634 eq10 -- backward demodulation 10,634
  subsumption eq635 rfl


@[equational_result]
theorem Equation2571_implies_Equation3464 (G : Type*) [Magma G] (h : Equation2571 G) : Equation3464 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq125 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.1 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.1.1 in 20
  have eq185 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq148 -- superposition 148,15, 15 into 148, unify on (0).2 in 15 and (0).2.1 in 148
  have eq523 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq185 eq11 -- superposition 11,185, 185 into 11, unify on (0).2 in 185 and (0).1.1 in 11
  have eq610 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq523 eq12 -- superposition 12,523, 523 into 12, unify on (0).2 in 523 and (0).1 in 12
  have eq634 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq148 eq610 -- forward demodulation 610,148
  have eq635 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq634 eq10 -- backward demodulation 10,634
  subsumption eq635 rfl


@[equational_result]
theorem Equation2571_implies_Equation3152 (G : Type*) [Magma G] (h : Equation2571 G) : Equation3152 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq21 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1 in 12
  have eq24 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq48 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq21 -- superposition 21,16, 16 into 21, unify on (0).2 in 16 and (0).1.1 in 21
  have eq55 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq48 eq10 -- backward demodulation 10,48
  have eq159 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq24 eq12 -- superposition 12,24, 24 into 12, unify on (0).2 in 24 and (0).1 in 12
  have eq161 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq16 eq159 -- forward demodulation 159,16
  have eq230 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq16 eq161 -- superposition 161,16, 16 into 161, unify on (0).2 in 16 and (0).2.1 in 161
  have eq565 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq230 eq11 -- superposition 11,230, 230 into 11, unify on (0).2 in 230 and (0).1.1 in 11
  have eq719 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq565 eq12 -- superposition 12,565, 565 into 12, unify on (0).2 in 565 and (0).1 in 12
  have eq728 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq161 eq719 -- forward demodulation 719,161
  have eq864 : sK0 ≠ sK0 := superpose eq728 eq55 -- superposition 55,728, 728 into 55, unify on (0).2 in 728 and (0).2 in 55
  subsumption eq864 rfl


@[equational_result]
theorem Equation2571_implies_Equation3058 (G : Type*) [Magma G] (h : Equation2571 G) : Equation3058 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq125 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.1 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.1.1 in 20
  have eq185 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq148 -- superposition 148,15, 15 into 148, unify on (0).2 in 15 and (0).2.1 in 148
  have eq523 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq185 eq11 -- superposition 11,185, 185 into 11, unify on (0).2 in 185 and (0).1.1 in 11
  have eq610 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq523 eq12 -- superposition 12,523, 523 into 12, unify on (0).2 in 523 and (0).1 in 12
  have eq634 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq148 eq610 -- forward demodulation 610,148
  have eq635 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq634 eq10 -- backward demodulation 10,634
  subsumption eq635 eq634


@[equational_result]
theorem Equation2571_implies_Equation2746 (G : Type*) [Magma G] (h : Equation2571 G) : Equation2746 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq17 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq39 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq151 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1 in 12
  have eq161 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq15 eq151 -- forward demodulation 151,15
  have eq230 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq161 -- superposition 161,15, 15 into 161, unify on (0).2 in 15 and (0).2.1 in 161
  have eq570 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq230 eq11 -- superposition 11,230, 230 into 11, unify on (0).2 in 230 and (0).1.1 in 11
  have eq702 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq570 eq12 -- superposition 12,570, 570 into 12, unify on (0).2 in 570 and (0).1 in 12
  have eq727 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq161 eq702 -- forward demodulation 702,161
  have eq821 : sK0 ≠ sK0 := superpose eq727 eq17 -- superposition 17,727, 727 into 17, unify on (0).2 in 727 and (0).2 in 17
  subsumption eq821 rfl


@[equational_result]
theorem Equation2571_implies_Equation2662 (G : Type*) [Magma G] (h : Equation2571 G) : Equation2662 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq21 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1 in 12
  have eq51 : sK0 ≠ sK0 := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq51 rfl


@[equational_result]
theorem Equation2571_implies_Equation2652 (G : Type*) [Magma G] (h : Equation2571 G) : Equation2652 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq26 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.2 in 11
  have eq125 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.1 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.1.1 in 20
  have eq185 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq148 -- superposition 148,15, 15 into 148, unify on (0).2 in 15 and (0).2.1 in 148
  have eq523 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq185 eq11 -- superposition 11,185, 185 into 11, unify on (0).2 in 185 and (0).1.1 in 11
  have eq607 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq523 eq26 -- superposition 26,523, 523 into 26, unify on (0).2 in 523 and (0).2.1.1 in 26
  have eq610 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq523 eq12 -- superposition 12,523, 523 into 12, unify on (0).2 in 523 and (0).1 in 12
  have eq633 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq148 eq607 -- forward demodulation 607,148
  have eq634 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq633 eq10 -- backward demodulation 10,633
  have eq635 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq148 eq610 -- forward demodulation 610,148
  have eq653 : sK0 ≠ sK0 := superpose eq635 eq634 -- superposition 634,635, 635 into 634, unify on (0).2 in 635 and (0).2 in 634
  subsumption eq653 rfl


@[equational_result]
theorem Equation2571_implies_Equation2466 (G : Type*) [Magma G] (h : Equation2571 G) : Equation2466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq21 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1 in 12
  have eq48 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq15 eq21 -- superposition 21,15, 15 into 21, unify on (0).2 in 15 and (0).1.1 in 21
  have eq125 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.1 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.1.1 in 20
  have eq185 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq148 -- superposition 148,15, 15 into 148, unify on (0).2 in 15 and (0).2.1 in 148
  have eq523 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq185 eq11 -- superposition 11,185, 185 into 11, unify on (0).2 in 185 and (0).1.1 in 11
  have eq610 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq523 eq12 -- superposition 12,523, 523 into 12, unify on (0).2 in 523 and (0).1 in 12
  have eq634 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq148 eq610 -- forward demodulation 610,148
  have eq635 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq634 eq10 -- backward demodulation 10,634
  subsumption eq635 eq48


@[equational_result]
theorem Equation2571_implies_Equation1629 (G : Type*) [Magma G] (h : Equation2571 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1.2 in 8
  have eq20 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).1 in 11
  have eq22 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  have eq48 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.1 in 20
  have eq81 : sK0 ≠ sK0 := superpose eq48 eq22 -- superposition 22,48, 48 into 22, unify on (0).2 in 48 and (0).2 in 22
  subsumption eq81 rfl


@[equational_result]
theorem Equation2571_implies_Equation1731 (G : Type*) [Magma G] (h : Equation2571 G) : Equation1731 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq23 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  have eq26 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq151 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq26 eq12 -- superposition 12,26, 26 into 12, unify on (0).2 in 26 and (0).1 in 12
  have eq161 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq15 eq151 -- forward demodulation 151,15
  have eq230 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq161 -- superposition 161,15, 15 into 161, unify on (0).2 in 15 and (0).2.1 in 161
  have eq570 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq230 eq11 -- superposition 11,230, 230 into 11, unify on (0).2 in 230 and (0).1.1 in 11
  have eq702 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq570 eq12 -- superposition 12,570, 570 into 12, unify on (0).2 in 570 and (0).1 in 12
  have eq727 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq161 eq702 -- forward demodulation 702,161
  have eq806 : sK0 ≠ sK0 := superpose eq727 eq23 -- superposition 23,727, 727 into 23, unify on (0).2 in 727 and (0).2 in 23
  subsumption eq806 rfl


@[equational_result]
theorem Equation2571_implies_Equation1637 (G : Type*) [Magma G] (h : Equation2571 G) : Equation1637 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq21 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1 in 12
  have eq48 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq15 eq21 -- superposition 21,15, 15 into 21, unify on (0).2 in 15 and (0).1.1 in 21
  have eq125 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.1 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.1.1 in 20
  have eq185 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq148 -- superposition 148,15, 15 into 148, unify on (0).2 in 15 and (0).2.1 in 148
  have eq570 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq185 eq11 -- superposition 11,185, 185 into 11, unify on (0).2 in 185 and (0).1.1 in 11
  have eq702 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq570 eq12 -- superposition 12,570, 570 into 12, unify on (0).2 in 570 and (0).1 in 12
  have eq727 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq148 eq702 -- forward demodulation 702,148
  have eq728 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq727 eq10 -- backward demodulation 10,727
  subsumption eq728 eq48


@[equational_result]
theorem Equation2571_implies_Equation3537 (G : Type*) [Magma G] (h : Equation2571 G) : Equation3537 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq125 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.1 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.1.1 in 20
  have eq185 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq148 -- superposition 148,15, 15 into 148, unify on (0).2 in 15 and (0).2.1 in 148
  have eq523 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq185 eq11 -- superposition 11,185, 185 into 11, unify on (0).2 in 185 and (0).1.1 in 11
  have eq610 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq523 eq12 -- superposition 12,523, 523 into 12, unify on (0).2 in 523 and (0).1 in 12
  have eq634 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq148 eq610 -- forward demodulation 610,148
  have eq635 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq634 eq10 -- backward demodulation 10,634
  subsumption eq635 rfl


@[equational_result]
theorem Equation2571_implies_Equation3820 (G : Type*) [Magma G] (h : Equation2571 G) : Equation3820 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq125 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.1 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.1.1 in 20
  have eq185 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq148 -- superposition 148,15, 15 into 148, unify on (0).2 in 15 and (0).2.1 in 148
  have eq523 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq185 eq11 -- superposition 11,185, 185 into 11, unify on (0).2 in 185 and (0).1.1 in 11
  have eq610 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq523 eq12 -- superposition 12,523, 523 into 12, unify on (0).2 in 523 and (0).1 in 12
  have eq634 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq148 eq610 -- forward demodulation 610,148
  have eq714 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq634 eq10 -- superposition 10,634, 634 into 10, unify on (0).2 in 634 and (0).2 in 10
  subsumption eq714 rfl


@[equational_result]
theorem Equation2571_implies_Equation1746 (G : Type*) [Magma G] (h : Equation2571 G) : Equation1746 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq125 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.1 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.1.1 in 20
  have eq185 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq148 -- superposition 148,15, 15 into 148, unify on (0).2 in 15 and (0).2.1 in 148
  have eq523 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq185 eq11 -- superposition 11,185, 185 into 11, unify on (0).2 in 185 and (0).1.1 in 11
  have eq610 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq523 eq12 -- superposition 12,523, 523 into 12, unify on (0).2 in 523 and (0).1 in 12
  have eq634 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq148 eq610 -- forward demodulation 610,148
  have eq635 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq634 eq10 -- backward demodulation 10,634
  subsumption eq635 eq634


@[equational_result]
theorem Equation2571_implies_Equation23 (G : Type*) [Magma G] (h : Equation2571 G) : Equation23 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1.2 in 8
  have eq20 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).1 in 11
  have eq47 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.1 in 20
  have eq63 : sK0 ≠ sK0 := superpose eq47 eq9 -- superposition 9,47, 47 into 9, unify on (0).2 in 47 and (0).2 in 9
  subsumption eq63 rfl


@[equational_result]
theorem Equation2571_implies_Equation2706 (G : Type*) [Magma G] (h : Equation2571 G) : Equation2706 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq125 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.1 in 20
  have eq151 : sK0 ≠ sK0 := superpose eq125 eq10 -- superposition 10,125, 125 into 10, unify on (0).2 in 125 and (0).2 in 10
  subsumption eq151 rfl


@[equational_result]
theorem Equation2571_implies_Equation2733 (G : Type*) [Magma G] (h : Equation2571 G) : Equation2733 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq21 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1 in 12
  have eq26 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.2 in 11
  have eq48 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq15 eq21 -- superposition 21,15, 15 into 21, unify on (0).2 in 15 and (0).1.1 in 21
  have eq125 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.1 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.1.1 in 20
  have eq185 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq148 -- superposition 148,15, 15 into 148, unify on (0).2 in 15 and (0).2.1 in 148
  have eq523 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq185 eq11 -- superposition 11,185, 185 into 11, unify on (0).2 in 185 and (0).1.1 in 11
  have eq607 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq523 eq26 -- superposition 26,523, 523 into 26, unify on (0).2 in 523 and (0).2.1.1 in 26
  have eq633 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq148 eq607 -- forward demodulation 607,148
  have eq634 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq633 eq10 -- backward demodulation 10,633
  subsumption eq634 eq48


@[equational_result]
theorem Equation2571_implies_Equation2605 (G : Type*) [Magma G] (h : Equation2571 G) : Equation2605 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK2) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq125 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.1 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.1.1 in 20
  have eq185 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq148 -- superposition 148,15, 15 into 148, unify on (0).2 in 15 and (0).2.1 in 148
  have eq523 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq185 eq11 -- superposition 11,185, 185 into 11, unify on (0).2 in 185 and (0).1.1 in 11
  have eq610 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq523 eq12 -- superposition 12,523, 523 into 12, unify on (0).2 in 523 and (0).1 in 12
  have eq634 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq148 eq610 -- forward demodulation 610,148
  have eq635 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq634 eq10 -- backward demodulation 10,634
  subsumption eq635 eq634


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
theorem Equation4517_implies_Equation4384 (G : Type*) [Magma G] (h : Equation4517 G) : Equation4384 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X2) ◇ X5) = (X4 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = (X0 ◇ (X4 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X3 ◇ X1))) = (X4 ◇ (X5 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.2 in 17
  have eq70 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq244 (X0 X2 X3 X4 X5 : G) : (sK0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ≠ (sK0 ◇ (X5 ◇ sK0)) := superpose eq12 eq70 -- superposition 70,12, 12 into 70, unify on (0).2 in 12 and (0).1.2 in 70
  subsumption eq244 eq51


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
theorem Equation4517_implies_Equation4510 (G : Type*) [Magma G] (h : Equation4517 G) : Equation4510 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X2) ◇ X5) = (X4 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = (X0 ◇ (X4 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X3 ◇ X1))) = (X4 ◇ (X5 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.2 in 17
  have eq77 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq244 (X0 X2 X3 X4 X5 : G) : (sK0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ≠ (sK0 ◇ (X5 ◇ sK2)) := superpose eq12 eq77 -- superposition 77,12, 12 into 77, unify on (0).2 in 12 and (0).1.2 in 77
  subsumption eq244 eq51


@[equational_result]
theorem Equation4517_implies_Equation4470 (G : Type*) [Magma G] (h : Equation4517 G) : Equation4470 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X2) ◇ X5) = (X4 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = (X0 ◇ (X4 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X3 ◇ X1))) = (X4 ◇ (X5 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.2 in 17
  have eq77 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq244 (X0 X2 X3 X4 X5 : G) : (sK0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ≠ (sK0 ◇ (X5 ◇ sK1)) := superpose eq12 eq77 -- superposition 77,12, 12 into 77, unify on (0).2 in 12 and (0).1.2 in 77
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
theorem Equation4517_implies_Equation4475 (G : Type*) [Magma G] (h : Equation4517 G) : Equation4475 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X2) ◇ X5) = (X4 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = (X0 ◇ (X4 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X3 ◇ X1))) = (X4 ◇ (X5 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.2 in 17
  have eq77 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq244 (X0 X2 X3 X4 X5 : G) : (sK0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ≠ (sK0 ◇ (X5 ◇ sK1)) := superpose eq12 eq77 -- superposition 77,12, 12 into 77, unify on (0).2 in 12 and (0).1.2 in 77
  subsumption eq244 eq51


@[equational_result]
theorem Equation4517_implies_Equation4508 (G : Type*) [Magma G] (h : Equation4517 G) : Equation4508 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X2) ◇ X5) = (X4 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = (X0 ◇ (X4 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X3 ◇ X1))) = (X4 ◇ (X5 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.2 in 17
  have eq77 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq244 (X0 X2 X3 X4 X5 : G) : (sK0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ≠ (sK0 ◇ (X5 ◇ sK2)) := superpose eq12 eq77 -- superposition 77,12, 12 into 77, unify on (0).2 in 12 and (0).1.2 in 77
  subsumption eq244 eq51


@[equational_result]
theorem Equation4517_implies_Equation4439 (G : Type*) [Magma G] (h : Equation4517 G) : Equation4439 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X2) ◇ X5) = (X4 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = (X0 ◇ (X4 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X3 ◇ X1))) = (X4 ◇ (X5 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.2 in 17
  have eq77 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq244 (X0 X2 X3 X4 X5 : G) : (sK0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ≠ (sK0 ◇ (X5 ◇ sK0)) := superpose eq12 eq77 -- superposition 77,12, 12 into 77, unify on (0).2 in 12 and (0).1.2 in 77
  subsumption eq244 eq51


@[equational_result]
theorem Equation4517_implies_Equation4512 (G : Type*) [Magma G] (h : Equation4517 G) : Equation4512 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X2) ◇ X5) = (X4 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = (X0 ◇ (X4 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X3 ◇ X1))) = (X4 ◇ (X5 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.2 in 17
  have eq77 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq244 (X0 X2 X3 X4 X5 : G) : (sK0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ≠ (sK0 ◇ (X5 ◇ sK2)) := superpose eq12 eq77 -- superposition 77,12, 12 into 77, unify on (0).2 in 12 and (0).1.2 in 77
  subsumption eq244 eq51


@[equational_result]
theorem Equation4517_implies_Equation4471 (G : Type*) [Magma G] (h : Equation4517 G) : Equation4471 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X2) ◇ X5) = (X4 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = (X0 ◇ (X4 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X3 ◇ X1))) = (X4 ◇ (X5 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.2 in 17
  have eq77 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq244 (X0 X2 X3 X4 X5 : G) : (sK0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ≠ (sK0 ◇ (X5 ◇ sK1)) := superpose eq12 eq77 -- superposition 77,12, 12 into 77, unify on (0).2 in 12 and (0).1.2 in 77
  subsumption eq244 eq51


@[equational_result]
theorem Equation4517_implies_Equation4438 (G : Type*) [Magma G] (h : Equation4517 G) : Equation4438 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X2) ◇ X5) = (X4 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = (X0 ◇ (X4 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X3 ◇ X1))) = (X4 ◇ (X5 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.2 in 17
  have eq77 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq244 (X0 X2 X3 X4 X5 : G) : (sK0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ≠ (sK0 ◇ (X5 ◇ sK0)) := superpose eq12 eq77 -- superposition 77,12, 12 into 77, unify on (0).2 in 12 and (0).1.2 in 77
  subsumption eq244 eq51


@[equational_result]
theorem Equation4517_implies_Equation4437 (G : Type*) [Magma G] (h : Equation4517 G) : Equation4437 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X2) ◇ X5) = (X4 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = (X0 ◇ (X4 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X3 ◇ X1))) = (X4 ◇ (X5 ◇ X2)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.2 in 17
  have eq77 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
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
theorem Equation1983_implies_Equation1082 (G : Type*) [Magma G] (h : Equation1983 G) : Equation1082 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq87 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq87 rfl


@[equational_result]
theorem Equation1983_implies_Equation4118 (G : Type*) [Magma G] (h : Equation1983 G) : Equation4118 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq22 (X1 X2 X3 : G) : (X1 ◇ X2) = (((X1 ◇ X3) ◇ X3) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq120 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).2 in 10
  subsumption eq120 rfl


@[equational_result]
theorem Equation1983_implies_Equation1171 (G : Type*) [Magma G] (h : Equation1983 G) : Equation1171 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq87 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq87 rfl


@[equational_result]
theorem Equation1983_implies_Equation1038 (G : Type*) [Magma G] (h : Equation1983 G) : Equation1038 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq87 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq87 rfl


@[equational_result]
theorem Equation4115_implies_Equation4623 (G : Type*) [Magma G] (h : Equation4115 G) : Equation4623 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X3) ◇ X3) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ sK3) := mod_symm nh
  have eq14 (X2 X3 X4 : G) : (X4 ◇ X4) = ((X3 ◇ X3) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq52 (X0 : G) : (X0 ◇ X0) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq52 eq14


@[equational_result]
theorem Equation4115_implies_Equation3660 (G : Type*) [Magma G] (h : Equation4115 G) : Equation3660 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X3) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq14 (X2 X3 X4 : G) : (X4 ◇ X4) = ((X3 ◇ X3) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq23 (X0 : G) : (X0 ◇ X0) ≠ ((X0 ◇ X0) ◇ (sK0 ◇ sK1)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).1 in 10
  subsumption eq23 eq14


@[equational_result]
theorem Equation4115_implies_Equation359 (G : Type*) [Magma G] (h : Equation4115 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X3) ◇ X3) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X2 X3 X4 : G) : (X4 ◇ X4) = ((X3 ◇ X3) ◇ X2) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1 in 8
  have eq15 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2 in 8
  have eq25 (X0 : G) : (X0 ◇ X0) ≠ ((X0 ◇ X0) ◇ sK0) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).1 in 9
  subsumption eq25 eq13


@[equational_result]
theorem Equation4115_implies_Equation4091 (G : Type*) [Magma G] (h : Equation4115 G) : Equation4091 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X3) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq14 (X2 X3 X4 : G) : (X4 ◇ X4) = ((X3 ◇ X3) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq54 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.1 in 10
  subsumption eq54 eq14


@[equational_result]
theorem Equation4115_implies_Equation3663 (G : Type*) [Magma G] (h : Equation4115 G) : Equation3663 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X3) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq14 (X2 X3 X4 : G) : (X4 ◇ X4) = ((X3 ◇ X3) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq26 (X0 : G) : (X0 ◇ X0) ≠ ((X0 ◇ X0) ◇ (sK1 ◇ sK2)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).1 in 10
  subsumption eq26 eq14


@[equational_result]
theorem Equation4115_implies_Equation4099 (G : Type*) [Magma G] (h : Equation4115 G) : Equation4099 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X3) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq14 (X2 X3 X4 : G) : (X4 ◇ X4) = ((X3 ◇ X3) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq54 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK3) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.1 in 10
  subsumption eq54 eq14


@[equational_result]
theorem Equation3060_implies_Equation3072 (G : Type*) [Magma G] (h : Equation3060 G) : Equation3072 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK2) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq36 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X2) ◇ X1) ◇ X3) = X0 := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).1.1.1 in 9
  have eq39 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ X0) ◇ sK2) ◇ sK1) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.1.1 in 13
  subsumption eq39 eq36


@[equational_result]
theorem Equation1261_implies_Equation1226 (G : Type*) [Magma G] (h : Equation1261 G) : Equation1226 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X0 ◇ X4) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq34 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq13 eq16 -- superposition 16,13, 13 into 16, unify on (0).2 in 13 and (0).1.2 in 16
  have eq43 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := superpose eq34 eq10 -- backward demodulation 10,34
  subsumption eq43 eq11


@[equational_result]
theorem Equation1261_implies_Equation837 (G : Type*) [Magma G] (h : Equation1261 G) : Equation837 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X0 ◇ X4) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation1261_implies_Equation1242 (G : Type*) [Magma G] (h : Equation1261 G) : Equation1242 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X0 ◇ X4) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq34 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq13 eq16 -- superposition 16,13, 13 into 16, unify on (0).2 in 13 and (0).1.2 in 16
  have eq43 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := superpose eq34 eq10 -- backward demodulation 10,34
  subsumption eq43 eq11


@[equational_result]
theorem Equation1261_implies_Equation834 (G : Type*) [Magma G] (h : Equation1261 G) : Equation834 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X0 ◇ X4) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation1261_implies_Equation833 (G : Type*) [Magma G] (h : Equation1261 G) : Equation833 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X0 ◇ X4) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation1261_implies_Equation840 (G : Type*) [Magma G] (h : Equation1261 G) : Equation840 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X0 ◇ X4) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation1261_implies_Equation1246 (G : Type*) [Magma G] (h : Equation1261 G) : Equation1246 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X0 ◇ X4) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq34 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq13 eq16 -- superposition 16,13, 13 into 16, unify on (0).2 in 13 and (0).1.2 in 16
  have eq43 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) := superpose eq34 eq10 -- backward demodulation 10,34
  subsumption eq43 eq11


@[equational_result]
theorem Equation545_implies_Equation4675 (G : Type*) [Magma G] (h : Equation545 G) : Equation4675 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq25 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq47 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq25 -- forward demodulation 25,11
  have eq48 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq47 -- forward demodulation 47,9
  have eq49 (X0 X3 X4 : G) : (X0 ◇ X3) = (X4 ◇ X3) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq73 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ ((X0 ◇ sK3) ◇ sK2) := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2.1 in 10
  subsumption eq73 eq49


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
theorem Equation545_implies_Equation4086 (G : Type*) [Magma G] (h : Equation545 G) : Equation4086 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK0) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq25 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq47 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq25 -- forward demodulation 25,11
  have eq48 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq47 -- forward demodulation 47,9
  have eq49 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq73 (X0 : G) : (sK0 ◇ sK0) ≠ (((X0 ◇ sK0) ◇ sK2) ◇ sK0) := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2.1.1 in 10
  subsumption eq73 eq49


@[equational_result]
theorem Equation545_implies_Equation3918 (G : Type*) [Magma G] (h : Equation545 G) : Equation3918 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq25 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq47 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq25 -- forward demodulation 25,11
  have eq48 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq47 -- forward demodulation 47,9
  have eq49 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq73 (X0 : G) : (X0 ◇ sK1) ≠ ((sK0 ◇ (X0 ◇ sK1)) ◇ sK1) := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).1 in 10
  subsumption eq73 eq49


@[equational_result]
theorem Equation545_implies_Equation4284 (G : Type*) [Magma G] (h : Equation545 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq19 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq25 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq47 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq25 -- forward demodulation 25,11
  have eq48 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq47 -- forward demodulation 47,9
  have eq49 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq86 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2 in 10
  have eq171 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X4 ◇ (X2 ◇ X1)))) = X1 := superpose eq49 eq19 -- superposition 19,49, 49 into 19, unify on (0).2 in 49 and (0).1.2.2.2 in 19
  have eq209 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))))) = (X4 ◇ (X5 ◇ X3)) := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).2.2.2 in 11
  have eq217 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := superpose eq171 eq209 -- forward demodulation 209,171
  have eq281 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK1)) ≠ (X1 ◇ (sK1 ◇ sK1)) := superpose eq49 eq86 -- superposition 86,49, 49 into 86, unify on (0).2 in 49 and (0).1.2 in 86
  subsumption eq281 eq217


@[equational_result]
theorem Equation545_implies_Equation4320 (G : Type*) [Magma G] (h : Equation545 G) : Equation4320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq20 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq23 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK0)) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).1 in 13
  have eq26 (X0 X1 : G) : (X0 ◇ (sK0 ◇ sK0)) ≠ (X1 ◇ (sK1 ◇ sK0)) := superpose eq12 eq23 -- superposition 23,12, 12 into 23, unify on (0).2 in 12 and (0).1 in 23
  have eq30 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq52 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq30 -- forward demodulation 30,11
  have eq53 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq52 -- forward demodulation 52,9
  have eq54 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq53 -- forward demodulation 53,9
  have eq188 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X4 ◇ (X2 ◇ X1)))) = X1 := superpose eq54 eq20 -- superposition 20,54, 54 into 20, unify on (0).2 in 54 and (0).1.2.2.2 in 20
  have eq226 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))))) = (X4 ◇ (X5 ◇ X3)) := superpose eq20 eq11 -- superposition 11,20, 20 into 11, unify on (0).2 in 20 and (0).2.2.2 in 11
  have eq234 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := superpose eq188 eq226 -- forward demodulation 226,188
  have eq300 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ sK0)) ≠ (X2 ◇ (sK1 ◇ sK0)) := superpose eq54 eq26 -- superposition 26,54, 54 into 26, unify on (0).2 in 54 and (0).1.2 in 26
  subsumption eq300 eq234


@[equational_result]
theorem Equation545_implies_Equation4374 (G : Type*) [Magma G] (h : Equation545 G) : Equation4374 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq22 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK1 ◇ sK2)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 eq14


@[equational_result]
theorem Equation545_implies_Equation422 (G : Type*) [Magma G] (h : Equation545 G) : Equation422 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq29 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq52 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq29 -- forward demodulation 29,11
  have eq53 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq52 -- forward demodulation 52,9
  have eq54 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq53 -- forward demodulation 53,9
  have eq80 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X1 := superpose eq54 eq9 -- superposition 9,54, 54 into 9, unify on (0).2 in 54 and (0).1.2.2.2 in 9
  have eq93 (X0 : G) : sK0 ≠ (sK0 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := superpose eq54 eq13 -- superposition 13,54, 54 into 13, unify on (0).2 in 54 and (0).2.2 in 13
  subsumption eq93 eq80


@[equational_result]
theorem Equation545_implies_Equation3939 (G : Type*) [Magma G] (h : Equation545 G) : Equation3939 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq25 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq47 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq25 -- forward demodulation 25,11
  have eq48 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq47 -- forward demodulation 47,9
  have eq49 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq85 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2 in 10
  subsumption eq85 eq49


@[equational_result]
theorem Equation545_implies_Equation476 (G : Type*) [Magma G] (h : Equation545 G) : Equation476 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq29 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq52 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq29 -- forward demodulation 29,11
  have eq53 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq52 -- forward demodulation 52,9
  have eq54 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq53 -- forward demodulation 53,9
  have eq80 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X1 := superpose eq54 eq9 -- superposition 9,54, 54 into 9, unify on (0).2 in 54 and (0).1.2.2.2 in 9
  have eq93 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := superpose eq54 eq13 -- superposition 13,54, 54 into 13, unify on (0).2 in 54 and (0).2.2 in 13
  subsumption eq93 eq80


@[equational_result]
theorem Equation545_implies_Equation4622 (G : Type*) [Magma G] (h : Equation545 G) : Equation4622 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq25 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq47 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq25 -- forward demodulation 25,11
  have eq48 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq47 -- forward demodulation 47,9
  have eq49 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq73 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((X0 ◇ sK2) ◇ sK1) := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2.1 in 10
  subsumption eq73 eq49


@[equational_result]
theorem Equation545_implies_Equation3890 (G : Type*) [Magma G] (h : Equation545 G) : Equation3890 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq26 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq48 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq26 -- forward demodulation 26,11
  have eq49 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq50 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq49 -- forward demodulation 49,9
  have eq74 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ (X0 ◇ sK1)) ◇ sK0) := superpose eq50 eq10 -- superposition 10,50, 50 into 10, unify on (0).2 in 50 and (0).2.1.2 in 10
  subsumption eq74 eq50


@[equational_result]
theorem Equation545_implies_Equation3864 (G : Type*) [Magma G] (h : Equation545 G) : Equation3864 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq25 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq47 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq25 -- forward demodulation 25,11
  have eq48 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq47 -- forward demodulation 47,9
  have eq49 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq73 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK0 ◇ (X0 ◇ sK1)) ◇ sK0) := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2.1.2 in 10
  subsumption eq73 eq49


@[equational_result]
theorem Equation545_implies_Equation4693 (G : Type*) [Magma G] (h : Equation545 G) : Equation4693 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK3 ◇ sK4) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq25 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq47 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq25 -- forward demodulation 25,11
  have eq48 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq47 -- forward demodulation 47,9
  have eq49 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq73 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ ((X0 ◇ sK4) ◇ sK2) := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2.1 in 10
  subsumption eq73 eq49


@[equational_result]
theorem Equation545_implies_Equation370 (G : Type*) [Magma G] (h : Equation545 G) : Equation370 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq25 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq47 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq25 -- forward demodulation 25,11
  have eq48 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq47 -- forward demodulation 47,9
  have eq49 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq73 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ sK2) ◇ sK0) := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2.1 in 10
  subsumption eq73 eq49


@[equational_result]
theorem Equation545_implies_Equation466 (G : Type*) [Magma G] (h : Equation545 G) : Equation466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq26 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq48 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq26 -- forward demodulation 26,11
  have eq49 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq50 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq49 -- forward demodulation 49,9
  have eq76 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X1 := superpose eq50 eq9 -- superposition 9,50, 50 into 9, unify on (0).2 in 50 and (0).1.2.2.2 in 9
  have eq88 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := superpose eq50 eq10 -- superposition 10,50, 50 into 10, unify on (0).2 in 50 and (0).2.2 in 10
  subsumption eq88 eq76


@[equational_result]
theorem Equation545_implies_Equation4296 (G : Type*) [Magma G] (h : Equation545 G) : Equation4296 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK1)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  have eq26 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq48 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq26 -- forward demodulation 26,11
  have eq49 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq50 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq49 -- forward demodulation 49,9
  have eq109 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq50 eq19 -- superposition 19,50, 50 into 19, unify on (0).2 in 50 and (0).1.2 in 19
  subsumption eq109 rfl


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
theorem Equation545_implies_Equation3928 (G : Type*) [Magma G] (h : Equation545 G) : Equation3928 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq25 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq47 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq25 -- forward demodulation 25,11
  have eq48 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq47 -- forward demodulation 47,9
  have eq49 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq85 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2 in 10
  subsumption eq85 eq49


@[equational_result]
theorem Equation545_implies_Equation4362 (G : Type*) [Magma G] (h : Equation545 G) : Equation4362 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq19 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq25 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq47 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq25 -- forward demodulation 25,11
  have eq48 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq47 -- forward demodulation 47,9
  have eq49 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq86 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (X0 ◇ sK2)) := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2.2 in 10
  have eq171 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X4 ◇ (X2 ◇ X1)))) = X1 := superpose eq49 eq19 -- superposition 19,49, 49 into 19, unify on (0).2 in 49 and (0).1.2.2.2 in 19
  have eq209 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))))) = (X4 ◇ (X5 ◇ X3)) := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).2.2.2 in 11
  have eq217 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := superpose eq171 eq209 -- forward demodulation 209,171
  have eq285 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X1 ◇ (X0 ◇ sK2)) := superpose eq14 eq86 -- superposition 86,14, 14 into 86, unify on (0).2 in 14 and (0).2 in 86
  subsumption eq285 eq217


@[equational_result]
theorem Equation545_implies_Equation4642 (G : Type*) [Magma G] (h : Equation545 G) : Equation4642 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK2 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq25 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq47 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq25 -- forward demodulation 25,11
  have eq48 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq47 -- forward demodulation 47,9
  have eq49 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq73 (X0 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ ((X0 ◇ sK0) ◇ sK0) := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2.1 in 10
  subsumption eq73 eq49


@[equational_result]
theorem Equation545_implies_Equation3931 (G : Type*) [Magma G] (h : Equation545 G) : Equation3931 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq25 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq47 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq25 -- forward demodulation 25,11
  have eq48 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq47 -- forward demodulation 47,9
  have eq49 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq85 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2 in 10
  subsumption eq85 eq49


@[equational_result]
theorem Equation545_implies_Equation426 (G : Type*) [Magma G] (h : Equation545 G) : Equation426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq26 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq48 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq26 -- forward demodulation 26,11
  have eq49 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq50 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq49 -- forward demodulation 49,9
  have eq76 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X1 := superpose eq50 eq9 -- superposition 9,50, 50 into 9, unify on (0).2 in 50 and (0).1.2.2.2 in 9
  have eq87 (X0 : G) : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (X0 ◇ sK0)))) := superpose eq50 eq10 -- superposition 10,50, 50 into 10, unify on (0).2 in 50 and (0).2.2.2.2 in 10
  subsumption eq87 eq76


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
theorem Equation545_implies_Equation442 (G : Type*) [Magma G] (h : Equation545 G) : Equation442 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq29 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq52 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq29 -- forward demodulation 29,11
  have eq53 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq52 -- forward demodulation 52,9
  have eq54 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq53 -- forward demodulation 53,9
  have eq80 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X1 := superpose eq54 eq9 -- superposition 9,54, 54 into 9, unify on (0).2 in 54 and (0).1.2.2.2 in 9
  have eq93 (X0 : G) : sK0 ≠ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := superpose eq54 eq13 -- superposition 13,54, 54 into 13, unify on (0).2 in 54 and (0).2 in 13
  subsumption eq93 eq80


@[equational_result]
theorem Equation545_implies_Equation413 (G : Type*) [Magma G] (h : Equation545 G) : Equation413 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq26 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq48 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq26 -- forward demodulation 26,11
  have eq49 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq50 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq49 -- forward demodulation 49,9
  have eq76 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X1 := superpose eq50 eq9 -- superposition 9,50, 50 into 9, unify on (0).2 in 50 and (0).1.2.2.2 in 9
  have eq88 (X0 : G) : sK0 ≠ (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := superpose eq50 eq10 -- superposition 10,50, 50 into 10, unify on (0).2 in 50 and (0).2.2 in 10
  subsumption eq88 eq76


@[equational_result]
theorem Equation545_implies_Equation3893 (G : Type*) [Magma G] (h : Equation545 G) : Equation3893 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq25 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq47 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq25 -- forward demodulation 25,11
  have eq48 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq47 -- forward demodulation 47,9
  have eq49 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq73 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ (X0 ◇ sK2)) ◇ sK0) := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2.1.2 in 10
  subsumption eq73 eq49


@[equational_result]
theorem Equation545_implies_Equation436 (G : Type*) [Magma G] (h : Equation545 G) : Equation436 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq29 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq52 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq29 -- forward demodulation 29,11
  have eq53 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq52 -- forward demodulation 52,9
  have eq54 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq53 -- forward demodulation 53,9
  have eq80 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X1 := superpose eq54 eq9 -- superposition 9,54, 54 into 9, unify on (0).2 in 54 and (0).1.2.2.2 in 9
  have eq95 (X0 : G) : sK0 ≠ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq54 eq13 -- superposition 13,54, 54 into 13, unify on (0).2 in 54 and (0).2 in 13
  subsumption eq95 eq80


@[equational_result]
theorem Equation545_implies_Equation4360 (G : Type*) [Magma G] (h : Equation545 G) : Equation4360 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq19 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq25 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq47 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq25 -- forward demodulation 25,11
  have eq48 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq47 -- forward demodulation 47,9
  have eq49 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq86 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK3 ◇ sK2)) := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2 in 10
  have eq171 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X4 ◇ (X2 ◇ X1)))) = X1 := superpose eq49 eq19 -- superposition 19,49, 49 into 19, unify on (0).2 in 49 and (0).1.2.2.2 in 19
  have eq209 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))))) = (X4 ◇ (X5 ◇ X3)) := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).2.2.2 in 11
  have eq217 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := superpose eq171 eq209 -- forward demodulation 209,171
  have eq281 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK2)) ≠ (X1 ◇ (sK3 ◇ sK2)) := superpose eq49 eq86 -- superposition 86,49, 49 into 86, unify on (0).2 in 49 and (0).1.2 in 86
  subsumption eq281 eq217


@[equational_result]
theorem Equation545_implies_Equation4304 (G : Type*) [Magma G] (h : Equation545 G) : Equation4304 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq19 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq26 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq48 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq11 eq26 -- forward demodulation 26,11
  have eq49 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = (X4 ◇ X3) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq50 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ X3) := superpose eq9 eq49 -- forward demodulation 49,9
  have eq87 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (X0 ◇ sK1)) := superpose eq50 eq10 -- superposition 10,50, 50 into 10, unify on (0).2 in 50 and (0).2.2 in 10
  have eq179 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X4 ◇ (X2 ◇ X1)))) = X1 := superpose eq50 eq19 -- superposition 19,50, 50 into 19, unify on (0).2 in 50 and (0).1.2.2.2 in 19
  have eq217 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))))) = (X4 ◇ (X5 ◇ X3)) := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).2.2.2 in 11
  have eq225 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := superpose eq179 eq217 -- forward demodulation 217,179
  have eq228 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X1 ◇ (X0 ◇ sK1)) := superpose eq14 eq87 -- superposition 87,14, 14 into 87, unify on (0).2 in 14 and (0).2 in 87
  subsumption eq228 eq225


@[equational_result]
theorem Equation831_implies_Equation1631 (G : Type*) [Magma G] (h : Equation831 G) : Equation1631 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X4 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq19 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq19 eq12


@[equational_result]
theorem Equation831_implies_Equation1227 (G : Type*) [Magma G] (h : Equation831 G) : Equation1227 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X4 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq19 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq19 eq12


@[equational_result]
theorem Equation831_implies_Equation2452 (G : Type*) [Magma G] (h : Equation831 G) : Equation2452 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X4 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq24 : sK0 ≠ sK0 := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  subsumption eq24 rfl


@[equational_result]
theorem Equation831_implies_Equation3460 (G : Type*) [Magma G] (h : Equation831 G) : Equation3460 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X4 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq24 : sK0 ≠ sK0 := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  subsumption eq24 rfl


@[equational_result]
theorem Equation831_implies_Equation2446 (G : Type*) [Magma G] (h : Equation831 G) : Equation2446 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X4 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq24 : sK0 ≠ sK0 := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  subsumption eq24 rfl


@[equational_result]
theorem Equation831_implies_Equation1633 (G : Type*) [Magma G] (h : Equation831 G) : Equation1633 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X4 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq19 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq19 eq12


@[equational_result]
theorem Equation412_implies_Equation8 (G : Type*) [Magma G] (h : Equation412 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq10 -- backward demodulation 10,11
  have eq15 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq9 -- backward demodulation 9,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation412_implies_Equation359 (G : Type*) [Magma G] (h : Equation412 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq10 -- backward demodulation 10,11
  have eq15 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq9 -- backward demodulation 9,13
  subsumption eq15 eq13


