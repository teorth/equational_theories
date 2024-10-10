import equational_theories.Superposition
import equational_theories.Equations.All
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

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
theorem Equation897_implies_Equation977 (G : Type*) [Magma G] (h : Equation897 G) : Equation977 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq25 (X0 : G) : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.2 in 10
  subsumption eq25 eq24


@[equational_result]
theorem Equation90_implies_Equation1498 (G : Type*) [Magma G] (h : Equation90 G) : Equation1498 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq22 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 eq19


@[equational_result]
theorem Equation908_implies_Equation945 (G : Type*) [Magma G] (h : Equation908 G) : Equation945 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X3 ◇ ((X3 ◇ X0) ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq37 (X1 X3 : G) : X1 = X3 := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).1 in 15
  have eq51 (X0 : G) : sK0 ≠ (sK1 ◇ X0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq51 eq37


@[equational_result]
theorem Equation909_implies_Equation3887 (G : Type*) [Magma G] (h : Equation909 G) : Equation3887 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq13 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq14 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).1.2 in 12
  have eq15 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq14 -- forward demodulation 14,11
  have eq18 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq23 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).1.2 in 18
  have eq25 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq11 eq23 -- forward demodulation 23,11
  have eq43 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.2.2 in 12
  have eq49 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq43 eq10 -- backward demodulation 10,43
  subsumption eq49 eq25


@[equational_result]
theorem Equation910_implies_Equation1629 (G : Type*) [Magma G] (h : Equation910 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := superpose eq10 eq8 -- backward demodulation 8,10
  have eq16 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X1 := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).1.2.2.2 in 11
  have eq19 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1.2.2 in 16
  have eq35 : sK0 ≠ sK0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2 in 9
  subsumption eq35 rfl


@[equational_result]
theorem Equation912_implies_Equation947 (G : Type*) [Magma G] (h : Equation912 G) : Equation947 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq20 (X0 : G) : sK0 ≠ (sK1 ◇ ((X0 ◇ sK0) ◇ (sK1 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.1 in 10
  subsumption eq20 eq14


@[equational_result]
theorem Equation912_implies_Equation989 (G : Type*) [Magma G] (h : Equation912 G) : Equation989 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X2 ◇ X1))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq25 (X0 : G) : sK0 ≠ (X0 ◇ ((sK2 ◇ sK2) ◇ (sK3 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq25 eq24


@[equational_result]
theorem Equation913_implies_Equation3151 (G : Type*) [Magma G] (h : Equation913 G) : Equation3151 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK1) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = (X0 ◇ (X1 ◇ (X3 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X3) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq25 (X0 X1 X3 X4 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X4 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X0)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq26 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq30 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ (X3 ◇ X0))) ◇ (X4 ◇ (X0 ◇ X1)))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq34 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X0)))) = X1 := superpose eq26 eq25 -- backward demodulation 25,26
  have eq45 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X3) ◇ X1) = (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq58 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X1))) = X3 := superpose eq45 eq12 -- backward demodulation 12,45
  have eq77 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X0 ◇ X1))) = X0 := superpose eq11 eq26 -- superposition 26,11, 11 into 26, unify on (0).2 in 11 and (0).1.1 in 26
  have eq93 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq77 eq30 -- backward demodulation 30,77
  have eq113 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ X1) = (((X4 ◇ (X2 ◇ X0)) ◇ (X5 ◇ X4)) ◇ (((X4 ◇ (X2 ◇ X0)) ◇ (X5 ◇ X4)) ◇ (X0 ◇ (X1 ◇ (X3 ◇ X0))))) := superpose eq11 eq58 -- superposition 58,11, 11 into 58, unify on (0).2 in 11 and (0).1.2.2 in 58
  have eq152 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X3 ◇ X0)) = X1 := superpose eq93 eq26 -- superposition 26,93, 93 into 26, unify on (0).2 in 93 and (0).1.1.2 in 26
  have eq163 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK0) ◇ sK2) := superpose eq93 eq10 -- superposition 10,93, 93 into 10, unify on (0).2 in 93 and (0).2.1 in 10
  have eq183 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X1))) = X3 := superpose eq26 eq34 -- superposition 34,26, 26 into 34, unify on (0).2 in 26 and (0).1.2.2.2 in 34
  have eq209 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq183 eq113 -- backward demodulation 113,183
  have eq214 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X1 := superpose eq209 eq152 -- backward demodulation 152,209
  have eq218 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq209 eq163 -- backward demodulation 163,209
  have eq294 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = X1 := superpose eq209 eq214 -- forward demodulation 214,209
  have eq295 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq209 eq294 -- forward demodulation 294,209
  subsumption eq218 eq295


@[equational_result]
theorem Equation916_implies_Equation1426 (G : Type*) [Magma G] (h : Equation916 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.2 in 10
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2.2 in 8
  have eq18 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq8 eq13 -- superposition 13,8, 8 into 13, unify on (0).2 in 8 and (0).2.2 in 13
  have eq20 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq18 -- forward demodulation 18,8
  have eq21 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq20 -- forward demodulation 20,10
  have eq22 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq21 eq11 -- backward demodulation 11,21
  have eq26 : sK0 ≠ sK0 := superpose eq22 eq9 -- superposition 9,22, 22 into 9, unify on (0).2 in 22 and (0).2 in 9
  subsumption eq26 rfl


@[equational_result]
theorem Equation916_implies_Equation359 (G : Type*) [Magma G] (h : Equation916 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq11 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2 in 8
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2.2 in 8
  have eq15 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq10 eq12 -- superposition 12,10, 10 into 12, unify on (0).2 in 10 and (0).1.2.2 in 12
  have eq18 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq8 eq13 -- superposition 13,8, 8 into 13, unify on (0).2 in 8 and (0).2.2 in 13
  have eq20 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq18 -- forward demodulation 18,8
  have eq21 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq20 -- forward demodulation 20,10
  have eq22 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq21 eq11 -- backward demodulation 11,21
  have eq24 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq28 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq24 eq9 -- superposition 9,24, 24 into 9, unify on (0).2 in 24 and (0).2 in 9
  subsumption eq28 rfl


@[equational_result]
theorem Equation916_implies_Equation3862 (G : Type*) [Magma G] (h : Equation916 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq11 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.2 in 10
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2.2 in 8
  have eq18 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq8 eq13 -- superposition 13,8, 8 into 13, unify on (0).2 in 8 and (0).2.2 in 13
  have eq20 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq18 -- forward demodulation 18,8
  have eq21 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq20 -- forward demodulation 20,10
  have eq22 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq21 eq11 -- backward demodulation 11,21
  have eq25 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq10 eq22 -- superposition 22,10, 10 into 22, unify on (0).2 in 10 and (0).1.1 in 22
  have eq26 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq22 eq25 -- forward demodulation 25,22
  have eq40 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).2 in 9
  subsumption eq40 rfl


@[equational_result]
theorem Equation916_implies_Equation47 (G : Type*) [Magma G] (h : Equation916 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2 in 8
  have eq16 : sK0 ≠ sK0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq16 rfl


@[equational_result]
theorem Equation916_implies_Equation642 (G : Type*) [Magma G] (h : Equation916 G) : Equation642 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq13 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.2 in 9
  have eq18 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq11 eq14 -- superposition 14,11, 11 into 14, unify on (0).2 in 11 and (0).1 in 14
  have eq19 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.2 in 14
  have eq21 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq19 -- forward demodulation 19,9
  have eq22 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq21 -- forward demodulation 21,11
  have eq23 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq22 eq12 -- backward demodulation 12,22
  have eq24 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq23 eq18 -- backward demodulation 18,23
  have eq26 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq24 eq10 -- backward demodulation 10,24
  subsumption eq26 eq13


@[equational_result]
theorem Equation922_implies_Equation955 (G : Type*) [Magma G] (h : Equation922 G) : Equation955 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq23 (X0 : G) : sK0 ≠ (X0 ◇ ((sK2 ◇ sK0) ◇ (sK3 ◇ sK0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq23 eq22


@[equational_result]
theorem Equation926_implies_Equation1564 (G : Type*) [Magma G] (h : Equation926 G) : Equation1564 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq19 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq19 eq11


@[equational_result]
theorem Equation927_implies_Equation741 (G : Type*) [Magma G] (h : Equation927 G) : Equation741 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK0 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = X1 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq44 (X2 X3 : G) : X2 = X3 := superpose eq16 eq16 -- superposition 16,16, 16 into 16, unify on (0).2 in 16 and (0).1 in 16
  have eq57 (X0 X1 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2.2 in 10
  subsumption eq57 eq44


@[equational_result]
theorem Equation930_implies_Equation782 (G : Type*) [Magma G] (h : Equation930 G) : Equation782 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq22 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1 in 16
  have eq32 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := superpose eq16 eq22 -- superposition 22,16, 16 into 22, unify on (0).2 in 16 and (0).2 in 22
  subsumption eq32 eq23


@[equational_result]
theorem Equation943_implies_Equation893 (G : Type*) [Magma G] (h : Equation943 G) : Equation893 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq13 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0))) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq17 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := superpose eq13 eq16 -- forward demodulation 16,13
  subsumption eq17 eq9


@[equational_result]
theorem Equation944_implies_Equation1765 (G : Type*) [Magma G] (h : Equation944 G) : Equation1765 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X0)) = (X3 ◇ (X2 ◇ (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X0) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq33 (X0 X1 X2 X3 X4 : G) : (((X4 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X0 ◇ X1)))) ◇ (((X2 ◇ X3) ◇ (X3 ◇ (X0 ◇ X1))) ◇ X1)) ◇ X3) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq34 (X1 X2 X3 : G) : ((X3 ◇ X2) ◇ X1) = ((X1 ◇ X2) ◇ X1) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.1.2 in 13
  have eq37 (X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X1) = (X4 ◇ (X2 ◇ (((X3 ◇ X2) ◇ X1) ◇ X4))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq49 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) := superpose eq13 eq34 -- superposition 34,13, 13 into 34, unify on (0).2 in 13 and (0).2 in 34
  have eq79 (X0 X1 X2 X3 X4 : G) : (((X4 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X1)) ◇ X3) = X1 := superpose eq49 eq33 -- backward demodulation 33,49
  have eq81 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = X1 := superpose eq49 eq79 -- forward demodulation 79,49
  have eq85 (X1 X2 X3 X4 X5 : G) : (X2 ◇ (((X3 ◇ X2) ◇ X1) ◇ X4)) = (X5 ◇ (((X3 ◇ X2) ◇ X1) ◇ ((X2 ◇ (((X3 ◇ X2) ◇ X1) ◇ X4)) ◇ X5))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq133 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = X1 := superpose eq81 eq81 -- superposition 81,81, 81 into 81, unify on (0).2 in 81 and (0).1.1 in 81
  have eq161 (X1 X2 X3 X4 : G) : (X2 ◇ (((X3 ◇ X2) ◇ X1) ◇ X4)) = X1 := superpose eq133 eq85 -- backward demodulation 85,133
  have eq162 (X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X1) = (X4 ◇ X1) := superpose eq161 eq37 -- backward demodulation 37,161
  have eq178 (X0 X2 X3 : G) : (X3 ◇ X0) = X2 := superpose eq81 eq162 -- superposition 162,81, 81 into 162, unify on (0).2 in 81 and (0).1 in 162
  have eq204 (X0 : G) : sK0 ≠ (X0 ◇ ((sK0 ◇ sK2) ◇ sK2)) := superpose eq162 eq10 -- superposition 10,162, 162 into 10, unify on (0).2 in 162 and (0).2 in 10
  subsumption eq204 eq178


@[equational_result]
theorem Equation945_implies_Equation83 (G : Type*) [Magma G] (h : Equation945 G) : Equation83 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq25 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq25 eq23


@[equational_result]
theorem Equation947_implies_Equation3897 (G : Type*) [Magma G] (h : Equation947 G) : Equation3897 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X3 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2)))) = (X4 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X4 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X1) ◇ (X3 ◇ X1)) ◇ (X4 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X1)))))) = (X5 ◇ ((X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X1)))) ◇ (X5 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X1)) ◇ (X4 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X1))))))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq15 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X2) = (X4 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X4 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X2)))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq20 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq17 eq9 -- backward demodulation 9,17
  have eq21 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X2)) = (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2))))) := superpose eq17 eq11 -- backward demodulation 11,17
  have eq22 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X2)) = (X0 ◇ ((X3 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2)) := superpose eq17 eq12 -- backward demodulation 12,17
  have eq23 (X0 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2)))) = (X4 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X4 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2))))))) := superpose eq17 eq13 -- backward demodulation 13,17
  have eq24 (X0 X1 X3 X4 X5 : G) : ((X3 ◇ (X1 ◇ X1)) ◇ (X4 ◇ (X1 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X1)))))) = (X5 ◇ ((X1 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X5 ◇ ((X3 ◇ (X1 ◇ X1)) ◇ (X4 ◇ (X1 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X1))))))))) := superpose eq17 eq14 -- backward demodulation 14,17
  have eq25 (X0 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2) = (X4 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X4 ◇ ((X3 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2)))) := superpose eq17 eq15 -- backward demodulation 15,17
  have eq29 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq20 eq20 -- superposition 20,20, 20 into 20, unify on (0).2 in 20 and (0).1.2 in 20
  have eq30 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq29 eq20 -- superposition 20,29, 29 into 20, unify on (0).2 in 29 and (0).1.2 in 20
  have eq31 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq17 eq30 -- forward demodulation 30,17
  have eq34 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq21 eq21 -- superposition 21,21, 21 into 21, unify on (0).2 in 21 and (0).2.2.2 in 21
  have eq35 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq29 eq21 -- superposition 21,29, 29 into 21, unify on (0).2 in 29 and (0).2.2.2 in 21
  have eq37 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq21 eq21 -- superposition 21,21, 21 into 21, unify on (0).2 in 21 and (0).2.2 in 21
  have eq39 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq17 eq34 -- forward demodulation 34,17
  have eq40 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq17 eq39 -- forward demodulation 39,17
  have eq41 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) := superpose eq17 eq35 -- forward demodulation 35,17
  have eq42 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq17 eq41 -- forward demodulation 41,17
  have eq43 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq17 eq37 -- forward demodulation 37,17
  have eq44 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq20 eq43 -- forward demodulation 43,20
  have eq45 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq20 eq44 -- superposition 44,20, 20 into 44, unify on (0).2 in 20 and (0).1.2 in 44
  have eq47 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq17 eq45 -- forward demodulation 45,17
  have eq53 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))))) := superpose eq22 eq21 -- superposition 21,22, 22 into 21, unify on (0).2 in 22 and (0).2.2 in 21
  have eq60 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose eq17 eq53 -- forward demodulation 53,17
  have eq61 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq17 eq60 -- forward demodulation 60,17
  have eq76 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))))) = ((X2 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))))) := superpose eq21 eq17 -- superposition 17,21, 21 into 17, unify on (0).2 in 21 and (0).1.1 in 17
  have eq77 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2) ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2))) = ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2))) := superpose eq22 eq17 -- superposition 17,22, 22 into 17, unify on (0).2 in 22 and (0).1.1 in 17
  have eq82 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq20 eq17 -- superposition 17,20, 20 into 17, unify on (0).2 in 20 and (0).1.2 in 17
  have eq93 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).1.2 in 20
  have eq103 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).1.2.2 in 20
  have eq106 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))))) = (X3 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))))) := superpose eq17 eq76 -- forward demodulation 76,17
  have eq107 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))))) = (X3 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1)))))) := superpose eq17 eq106 -- forward demodulation 106,17
  have eq108 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))))) = (X3 ◇ (X1 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))))) := superpose eq17 eq107 -- forward demodulation 107,17
  have eq109 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))))) = (X3 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq17 eq108 -- forward demodulation 108,17
  have eq110 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X1 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) = (X5 ◇ ((X1 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X5 ◇ (X4 ◇ (X1 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1))))))))) := superpose eq109 eq24 -- backward demodulation 24,109
  have eq111 (X0 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2)))) = (X4 ◇ (X4 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2))))))) := superpose eq109 eq23 -- backward demodulation 23,109
  have eq112 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2))) = (X3 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2))) := superpose eq17 eq77 -- forward demodulation 77,17
  have eq113 (X0 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2) = (X4 ◇ (X4 ◇ ((X3 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2)))) := superpose eq112 eq25 -- backward demodulation 25,112
  have eq117 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq17 eq82 -- forward demodulation 82,17
  have eq118 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := superpose eq20 eq117 -- forward demodulation 117,20
  have eq121 (X0 X2 X3 X4 : G) : (X2 ◇ X2) = (X4 ◇ (X4 ◇ ((X3 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2)))) := superpose eq118 eq113 -- backward demodulation 113,118
  have eq122 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2))) = ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X2 ◇ X2))) := superpose eq118 eq112 -- backward demodulation 112,118
  have eq123 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2))) = (X3 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) := superpose eq17 eq122 -- forward demodulation 122,17
  have eq124 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2))) = (X3 ◇ (X2 ◇ (X2 ◇ X2))) := superpose eq17 eq123 -- forward demodulation 123,17
  have eq125 (X2 X4 : G) : (X2 ◇ X2) = (X4 ◇ (X4 ◇ (X2 ◇ (X2 ◇ X2)))) := superpose eq124 eq121 -- backward demodulation 121,124
  have eq144 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq20 eq93 -- superposition 93,20, 20 into 93, unify on (0).2 in 20 and (0).1.1 in 93
  have eq154 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq93 eq17 -- superposition 17,93, 93 into 17, unify on (0).2 in 93 and (0).1.2 in 17
  have eq156 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq103 eq144 -- forward demodulation 144,103
  have eq163 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq17 eq154 -- forward demodulation 154,17
  have eq164 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq17 eq163 -- forward demodulation 163,17
  have eq165 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq20 eq164 -- forward demodulation 164,20
  have eq166 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq118 eq165 -- forward demodulation 165,118
  have eq174 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq31 eq20 -- superposition 20,31, 31 into 20, unify on (0).2 in 31 and (0).1.2.2 in 20
  have eq182 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq31 eq17 -- superposition 17,31, 31 into 17, unify on (0).2 in 31 and (0).1.1 in 17
  have eq190 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq182 eq61 -- backward demodulation 61,182
  have eq191 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq182 eq42 -- backward demodulation 42,182
  have eq192 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq182 eq40 -- backward demodulation 40,182
  have eq273 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq174 eq174 -- superposition 174,174, 174 into 174, unify on (0).2 in 174 and (0).1 in 174
  have eq276 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) = ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) := superpose eq17 eq174 -- superposition 174,17, 17 into 174, unify on (0).2 in 17 and (0).2.2 in 174
  have eq283 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq174 eq20 -- superposition 20,174, 174 into 20, unify on (0).2 in 174 and (0).1.2 in 20
  have eq289 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq174 eq93 -- superposition 93,174, 174 into 93, unify on (0).2 in 174 and (0).1.2 in 93
  have eq305 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) = ((X2 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq17 eq276 -- forward demodulation 276,17
  have eq533 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq20 eq191 -- superposition 191,20, 20 into 191, unify on (0).2 in 20 and (0).2.1.2 in 191
  have eq577 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq17 eq533 -- forward demodulation 533,17
  have eq583 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X1 ◇ X1))) = ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq577 eq305 -- backward demodulation 305,577
  have eq693 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X1))) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq17 eq156 -- superposition 156,17, 17 into 156, unify on (0).2 in 17 and (0).1.2 in 156
  have eq717 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq156 eq20 -- superposition 20,156, 156 into 20, unify on (0).2 in 156 and (0).1.2 in 20
  have eq1025 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq717 eq190 -- superposition 190,717, 717 into 190, unify on (0).2 in 717 and (0).2.1 in 190
  have eq1047 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq17 eq1025 -- forward demodulation 1025,17
  have eq1167 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ (X1 ◇ X1))) = (X3 ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))))) := superpose eq21 eq273 -- superposition 273,21, 21 into 273, unify on (0).2 in 21 and (0).1.2 in 273
  have eq1238 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq273 eq190 -- superposition 190,273, 273 into 190, unify on (0).2 in 273 and (0).2.1 in 190
  have eq1424 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1))))))) := superpose eq190 eq111 -- superposition 111,190, 190 into 111, unify on (0).2 in 190 and (0).2.2 in 111
  have eq1428 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) ◇ (X3 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3)))) ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))))) := superpose eq17 eq111 -- superposition 111,17, 17 into 111, unify on (0).2 in 17 and (0).2.2 in 111
  have eq1456 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) = (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) := superpose eq111 eq17 -- superposition 17,111, 111 into 17, unify on (0).2 in 111 and (0).1.1 in 17
  have eq1653 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1))))))) := superpose eq17 eq1424 -- forward demodulation 1424,17
  have eq1654 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) ◇ (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))))))) := superpose eq17 eq1653 -- forward demodulation 1653,17
  have eq1655 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))))) := superpose eq17 eq1654 -- forward demodulation 1654,17
  have eq1656 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))))))) := superpose eq1047 eq1655 -- forward demodulation 1655,1047
  have eq1657 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))))) := superpose eq166 eq1656 -- forward demodulation 1656,166
  have eq1658 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) := superpose eq20 eq1657 -- forward demodulation 1657,20
  have eq1679 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) ◇ (X3 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X3))) ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))))) := superpose eq17 eq1428 -- forward demodulation 1428,17
  have eq1680 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X3 ◇ X3))))))) := superpose eq17 eq1679 -- forward demodulation 1679,17
  have eq1681 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3))))))) := superpose eq17 eq1680 -- forward demodulation 1680,17
  have eq1682 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ ((X3 ◇ X3) ◇ X3))))))) := superpose eq1047 eq1681 -- forward demodulation 1681,1047
  have eq1683 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X3))))))) := superpose eq166 eq1682 -- forward demodulation 1682,166
  have eq1684 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq20 eq1683 -- forward demodulation 1683,20
  have eq1772 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) = (X4 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1))))) ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) := superpose eq17 eq1456 -- forward demodulation 1456,17
  have eq1773 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) = (X4 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) := superpose eq17 eq1772 -- forward demodulation 1772,17
  have eq1774 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) := superpose eq17 eq1773 -- forward demodulation 1773,17
  have eq1775 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))))))) := superpose eq17 eq1774 -- forward demodulation 1774,17
  have eq1776 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))))))) := superpose eq17 eq1775 -- forward demodulation 1775,17
  have eq1777 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1)))))))) := superpose eq1047 eq1776 -- forward demodulation 1776,1047
  have eq1778 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))))) := superpose eq166 eq1777 -- forward demodulation 1777,166
  have eq1779 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))))) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1))))) := superpose eq20 eq1778 -- forward demodulation 1778,20
  have eq1780 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X1 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) = (X5 ◇ (X5 ◇ (X4 ◇ (X1 ◇ (X0 ◇ (X3 ◇ X1)))))) := superpose eq1779 eq110 -- backward demodulation 110,1779
  have eq1817 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq273 eq289 -- superposition 289,273, 273 into 289, unify on (0).2 in 273 and (0).1.1 in 289
  have eq2007 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X4 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))))) = (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)))))))) := superpose eq1780 eq1780 -- superposition 1780,1780, 1780 into 1780, unify on (0).2 in 1780 and (0).1.2.2 in 1780
  have eq2023 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))))) = (X4 ◇ (X4 ◇ (X3 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X1)))))) := superpose eq17 eq1780 -- superposition 1780,17, 17 into 1780, unify on (0).2 in 17 and (0).1.2.2 in 1780
  have eq2041 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) = (X4 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))))) := superpose eq190 eq1780 -- superposition 1780,190, 190 into 1780, unify on (0).2 in 190 and (0).1 in 1780
  have eq2049 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))))) = (X4 ◇ (X4 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X1 ◇ X1)))))) := superpose eq125 eq1780 -- superposition 1780,125, 125 into 1780, unify on (0).2 in 125 and (0).2.2.2.2.2.2 in 1780
  have eq2178 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) = (X4 ◇ (X4 ◇ (X3 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))))))) := superpose eq1780 eq20 -- superposition 20,1780, 1780 into 20, unify on (0).2 in 1780 and (0).1.2.2 in 20
  have eq2318 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X4 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))))) = (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq283 eq2007 -- forward demodulation 2007,283
  have eq2319 (X0 X1 X3 X4 : G) : (X3 ◇ (X0 ◇ X1)) = (X4 ◇ (X4 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))))) := superpose eq1817 eq2318 -- forward demodulation 2318,1817
  have eq2320 (X0 X1 X3 X4 : G) : (X3 ◇ (X0 ◇ X1)) = (X4 ◇ (X4 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1))))) := superpose eq20 eq2319 -- forward demodulation 2319,20
  have eq2321 (X0 X1 X3 X4 : G) : (X3 ◇ (X0 ◇ X1)) = (X4 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq1238 eq2320 -- forward demodulation 2320,1238
  have eq2394 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))))) = (X4 ◇ (X4 ◇ (X3 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X1)))))) := superpose eq17 eq2023 -- forward demodulation 2023,17
  have eq2395 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1)))))) = (X4 ◇ (X4 ◇ (X3 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X1)))))) := superpose eq1047 eq2394 -- forward demodulation 2394,1047
  have eq2396 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))) = (X4 ◇ (X4 ◇ (X3 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X1)))))) := superpose eq166 eq2395 -- forward demodulation 2395,166
  have eq2397 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X1))) = (X4 ◇ (X4 ◇ (X3 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X1)))))) := superpose eq20 eq2396 -- forward demodulation 2396,20
  have eq2434 (X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) = (X4 ◇ (X4 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))))) := superpose eq1658 eq2041 -- forward demodulation 2041,1658
  have eq2435 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X1))) = (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq1167 eq2434 -- forward demodulation 2434,1167
  have eq2436 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X1))) = (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq17 eq2435 -- forward demodulation 2435,17
  have eq2437 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq17 eq2436 -- forward demodulation 2436,17
  have eq2438 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))))) := superpose eq17 eq2437 -- forward demodulation 2437,17
  have eq2439 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1)))))) := superpose eq1047 eq2438 -- forward demodulation 2438,1047
  have eq2440 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq166 eq2439 -- forward demodulation 2439,166
  have eq2441 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq20 eq2440 -- forward demodulation 2440,20
  have eq2480 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))))) = (X4 ◇ (X4 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X1)))))) := superpose eq2441 eq2049 -- forward demodulation 2049,2441
  have eq2481 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X1))) = (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))))) := superpose eq2397 eq2480 -- forward demodulation 2480,2397
  have eq2482 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X1))) = (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))))))))) := superpose eq693 eq2481 -- forward demodulation 2481,693
  have eq2483 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X1))) = (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))))))))) := superpose eq583 eq2482 -- forward demodulation 2482,583
  have eq2484 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X1))) = (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq103 eq2483 -- forward demodulation 2483,103
  have eq2485 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X1))) = (X2 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq583 eq2484 -- forward demodulation 2484,583
  have eq2486 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X1))) = (X2 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))))) := superpose eq693 eq2485 -- forward demodulation 2485,693
  have eq2487 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X1))) = (X2 ◇ (X3 ◇ (X1 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))))) := superpose eq583 eq2486 -- forward demodulation 2486,583
  have eq2488 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X1))) = (X2 ◇ (X3 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq583 eq2487 -- forward demodulation 2487,583
  have eq2489 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X1))) = (X2 ◇ (X3 ◇ ((X1 ◇ X1) ◇ X1))) := superpose eq182 eq2488 -- forward demodulation 2488,182
  have eq2490 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X1))) = (X2 ◇ (X1 ◇ (X3 ◇ X1))) := superpose eq166 eq2489 -- forward demodulation 2489,166
  have eq2911 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) = (X4 ◇ (X4 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))))))) := superpose eq1684 eq2178 -- forward demodulation 2178,1684
  have eq2912 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) = (X4 ◇ (X4 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) := superpose eq1167 eq2911 -- forward demodulation 2911,1167
  have eq2913 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq2321 eq2912 -- forward demodulation 2912,2321
  have eq2915 (X0 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2)))) = (X4 ◇ (X4 ◇ (X3 ◇ (X0 ◇ X2)))) := superpose eq2913 eq111 -- backward demodulation 111,2913
  have eq2932 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1))))) = ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X4 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X1))))) := superpose eq2913 eq1779 -- backward demodulation 1779,2913
  have eq3658 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = ((X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := superpose eq2915 eq17 -- superposition 17,2915, 2915 into 17, unify on (0).2 in 2915 and (0).1.1 in 17
  have eq4091 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X3))))) = (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := superpose eq2932 eq3658 -- forward demodulation 3658,2932
  have eq4092 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X3))))) = (X4 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X2 ◇ X3))))) := superpose eq17 eq4091 -- forward demodulation 4091,17
  have eq4093 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X3))))) = (X4 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3))))) := superpose eq17 eq4092 -- forward demodulation 4092,17
  have eq4094 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X3))))) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) := superpose eq17 eq4093 -- forward demodulation 4093,17
  have eq4698 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq17 eq103 -- superposition 103,17, 17 into 103, unify on (0).2 in 17 and (0).2.2 in 103
  have eq4828 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1)))) := superpose eq2490 eq4698 -- forward demodulation 4698,2490
  have eq4829 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq166 eq4828 -- forward demodulation 4828,166
  have eq5843 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2))))) ◇ X2) = (((X0 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2))))) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2)))) := superpose eq118 eq192 -- superposition 192,118, 118 into 192, unify on (0).2 in 118 and (0).2.2 in 192
  have eq5917 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X2) = ((X0 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2))))) ◇ X2) := superpose eq4829 eq5843 -- forward demodulation 5843,4829
  have eq5918 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X2) = ((X0 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2))))) ◇ X2) := superpose eq4094 eq5917 -- forward demodulation 5917,4094
  have eq5919 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X2) = ((X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X2))))) ◇ X2) := superpose eq4094 eq5918 -- forward demodulation 5918,4094
  have eq5920 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))) ◇ X2) := superpose eq47 eq5919 -- forward demodulation 5919,47
  have eq5921 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq20 eq5920 -- forward demodulation 5920,20
  have eq6161 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq5921 eq10 -- superposition 10,5921, 5921 into 10, unify on (0).2 in 5921 and (0).2 in 10
  subsumption eq6161 rfl


@[equational_result]
theorem Equation947_implies_Equation723 (G : Type*) [Magma G] (h : Equation947 G) : Equation723 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK2 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X3 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq20 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq17 eq9 -- backward demodulation 9,17
  have eq82 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq20 eq17 -- superposition 17,20, 20 into 17, unify on (0).2 in 20 and (0).1.2 in 17
  have eq93 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).1.2 in 20
  have eq117 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq17 eq82 -- forward demodulation 82,17
  have eq118 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := superpose eq20 eq117 -- forward demodulation 117,20
  have eq154 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq93 eq17 -- superposition 17,93, 93 into 17, unify on (0).2 in 93 and (0).1.2 in 17
  have eq163 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq17 eq154 -- forward demodulation 154,17
  have eq164 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq17 eq163 -- forward demodulation 163,17
  have eq165 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq20 eq164 -- forward demodulation 164,20
  have eq166 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq118 eq165 -- forward demodulation 165,118
  have eq167 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq166 eq10 -- backward demodulation 10,166
  subsumption eq167 eq20


@[equational_result]
theorem Equation951_implies_Equation972 (G : Type*) [Magma G] (h : Equation951 G) : Equation972 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X0 ◇ X1))) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq23 (X0 : G) : sK0 ≠ (X0 ◇ ((sK2 ◇ sK1) ◇ (sK3 ◇ sK0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq23 eq22


@[equational_result]
theorem Equation960_implies_Equation1444 (G : Type*) [Magma G] (h : Equation960 G) : Equation1444 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ ((X3 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq18 (X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X4 ◇ X4))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ (X4 ◇ X4)) ◇ (X4 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq93 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) = X2 := superpose eq18 eq18 -- superposition 18,18, 18 into 18, unify on (0).2 in 18 and (0).1.1.2 in 18
  have eq120 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.2.2 in 9
  have eq400 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) = X0 := superpose eq120 eq15 -- superposition 15,120, 120 into 15, unify on (0).2 in 120 and (0).1.2 in 15
  have eq710 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (((X2 ◇ X3) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq17 eq26 -- superposition 26,17, 17 into 26, unify on (0).2 in 17 and (0).2.2 in 26
  have eq858 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) = (((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) ◇ (X1 ◇ X3)) := superpose eq9 eq400 -- superposition 400,9, 9 into 400, unify on (0).2 in 9 and (0).1.2.2 in 400
  have eq889 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) = (X3 ◇ (X1 ◇ X3)) := superpose eq710 eq858 -- forward demodulation 858,710
  have eq890 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2))) = X2 := superpose eq889 eq93 -- backward demodulation 93,889
  have eq1195 : sK0 ≠ sK0 := superpose eq890 eq10 -- superposition 10,890, 890 into 10, unify on (0).2 in 890 and (0).2 in 10
  subsumption eq1195 rfl


@[equational_result]
theorem Equation960_implies_Equation1478 (G : Type*) [Magma G] (h : Equation960 G) : Equation1478 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X4 ◇ X4))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq35 (X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ (X3 ◇ X3)) ◇ X3) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1 in 12
  have eq121 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq18 eq35 -- superposition 35,18, 18 into 35, unify on (0).2 in 18 and (0).1 in 35
  have eq298 : sK0 ≠ sK0 := superpose eq121 eq10 -- superposition 10,121, 121 into 10, unify on (0).2 in 121 and (0).2 in 10
  subsumption eq298 rfl


@[equational_result]
theorem Equation960_implies_Equation1560 (G : Type*) [Magma G] (h : Equation960 G) : Equation1560 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ ((X3 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq18 (X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X4 ◇ X4))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ (X4 ◇ X4)) ◇ (X4 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq93 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) = X2 := superpose eq18 eq18 -- superposition 18,18, 18 into 18, unify on (0).2 in 18 and (0).1.1.2 in 18
  have eq120 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.2.2 in 9
  have eq400 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) = X0 := superpose eq120 eq15 -- superposition 15,120, 120 into 15, unify on (0).2 in 120 and (0).1.2 in 15
  have eq710 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (((X2 ◇ X3) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq17 eq26 -- superposition 26,17, 17 into 26, unify on (0).2 in 17 and (0).2.2 in 26
  have eq858 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) = (((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) ◇ (X1 ◇ X3)) := superpose eq9 eq400 -- superposition 400,9, 9 into 400, unify on (0).2 in 9 and (0).1.2.2 in 400
  have eq889 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) = (X3 ◇ (X1 ◇ X3)) := superpose eq710 eq858 -- forward demodulation 858,710
  have eq890 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2))) = X2 := superpose eq889 eq93 -- backward demodulation 93,889
  have eq1195 : sK0 ≠ sK0 := superpose eq890 eq10 -- superposition 10,890, 890 into 10, unify on (0).2 in 890 and (0).2 in 10
  subsumption eq1195 rfl


@[equational_result]
theorem Equation960_implies_Equation364 (G : Type*) [Magma G] (h : Equation960 G) : Equation364 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ ((X3 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq18 (X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X4 ◇ X4))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq31 -- forward demodulation 31,12
  have eq100 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).1.2.2 in 18
  have eq116 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.2.2 in 9
  have eq172 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq16 eq16 -- superposition 16,16, 16 into 16, unify on (0).2 in 16 and (0).2.2 in 16
  have eq199 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq172 eq41 -- backward demodulation 41,172
  have eq415 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq116 eq199 -- superposition 199,116, 116 into 199, unify on (0).2 in 116 and (0).2.1 in 199
  have eq448 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq100 eq415 -- forward demodulation 415,100
  have eq632 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq448 eq10 -- superposition 10,448, 448 into 10, unify on (0).2 in 448 and (0).2 in 10
  subsumption eq632 rfl


@[equational_result]
theorem Equation960_implies_Equation3897 (G : Type*) [Magma G] (h : Equation960 G) : Equation3897 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ ((X3 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq18 (X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X4 ◇ X4))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ (X4 ◇ X4)) ◇ (X4 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq31 -- forward demodulation 31,12
  have eq93 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) = X2 := superpose eq18 eq18 -- superposition 18,18, 18 into 18, unify on (0).2 in 18 and (0).1.1.2 in 18
  have eq100 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).1.2.2 in 18
  have eq120 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.2.2 in 9
  have eq123 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq18 eq13 -- superposition 13,18, 18 into 13, unify on (0).2 in 18 and (0).1 in 13
  have eq172 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq17 eq17 -- superposition 17,17, 17 into 17, unify on (0).2 in 17 and (0).2.2 in 17
  have eq199 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq172 eq41 -- backward demodulation 41,172
  have eq400 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) = X0 := superpose eq120 eq15 -- superposition 15,120, 120 into 15, unify on (0).2 in 120 and (0).1.2 in 15
  have eq415 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X1 ◇ X0) ◇ X0) := superpose eq120 eq199 -- superposition 199,120, 120 into 199, unify on (0).2 in 120 and (0).2.1 in 199
  have eq447 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq100 eq415 -- forward demodulation 415,100
  have eq710 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (((X2 ◇ X3) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq17 eq26 -- superposition 26,17, 17 into 26, unify on (0).2 in 17 and (0).2.2 in 26
  have eq858 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) = (((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) ◇ (X1 ◇ X3)) := superpose eq9 eq400 -- superposition 400,9, 9 into 400, unify on (0).2 in 9 and (0).1.2.2 in 400
  have eq866 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ X0) = (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) := superpose eq400 eq400 -- superposition 400,400, 400 into 400, unify on (0).2 in 400 and (0).1.2 in 400
  have eq889 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) = (X3 ◇ (X1 ◇ X3)) := superpose eq710 eq858 -- forward demodulation 858,710
  have eq890 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2))) = X2 := superpose eq889 eq93 -- backward demodulation 93,889
  have eq899 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X2 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq447 eq866 -- forward demodulation 866,447
  have eq1168 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ (X2 ◇ X2)))) := superpose eq120 eq890 -- superposition 890,120, 120 into 890, unify on (0).2 in 120 and (0).1.2.2 in 890
  have eq1235 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq123 eq1168 -- forward demodulation 1168,123
  have eq1774 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ (sK2 ◇ sK0)) ◇ sK0) := superpose eq1235 eq10 -- superposition 10,1235, 1235 into 10, unify on (0).2 in 1235 and (0).2 in 10
  subsumption eq1774 eq899


@[equational_result]
theorem Equation960_implies_Equation4689 (G : Type*) [Magma G] (h : Equation960 G) : Equation4689 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK3 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ ((X3 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq18 (X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X4 ◇ X4))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ (X4 ◇ X4)) ◇ (X4 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq93 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) = X2 := superpose eq18 eq18 -- superposition 18,18, 18 into 18, unify on (0).2 in 18 and (0).1.1.2 in 18
  have eq120 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.2.2 in 9
  have eq123 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq18 eq13 -- superposition 13,18, 18 into 13, unify on (0).2 in 18 and (0).1 in 13
  have eq403 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) = X0 := superpose eq120 eq15 -- superposition 15,120, 120 into 15, unify on (0).2 in 120 and (0).1.2 in 15
  have eq711 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (((X2 ◇ X3) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq17 eq26 -- superposition 26,17, 17 into 26, unify on (0).2 in 17 and (0).2.2 in 26
  have eq859 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) = (((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) ◇ (X1 ◇ X3)) := superpose eq9 eq403 -- superposition 403,9, 9 into 403, unify on (0).2 in 9 and (0).1.2.2 in 403
  have eq890 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) = (X3 ◇ (X1 ◇ X3)) := superpose eq711 eq859 -- forward demodulation 859,711
  have eq891 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2))) = X2 := superpose eq890 eq93 -- backward demodulation 93,890
  have eq1169 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ (X2 ◇ X2)))) := superpose eq120 eq891 -- superposition 891,120, 120 into 891, unify on (0).2 in 120 and (0).1.2.2 in 891
  have eq1236 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq123 eq1169 -- forward demodulation 1169,123
  have eq1775 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ ((X0 ◇ sK1) ◇ sK2) := superpose eq1236 eq10 -- superposition 10,1236, 1236 into 10, unify on (0).2 in 1236 and (0).2 in 10
  subsumption eq1775 eq1236


@[equational_result]
theorem Equation961_implies_Equation3026 (G : Type*) [Magma G] (h : Equation961 G) : Equation3026 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X2)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq24 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1)))) = (((X4 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))))) ◇ X3) ◇ ((X5 ◇ ((X4 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))))) ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.2 in 12
  have eq25 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X2) = (((X4 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X2)) ◇ X1) ◇ ((X5 ◇ ((X4 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X2)) ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1)))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.2 in 12
  have eq35 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = (((X3 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) ◇ X2) ◇ (X0 ◇ X0)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.1.2 in 17
  have eq40 (X1 X2 X3 : G) : (((X2 ◇ X3) ◇ (X2 ◇ X3)) ◇ (X1 ◇ X2)) = X3 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1 in 12
  have eq42 (X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X2 ◇ X2)))) = X3 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.2.1 in 9
  have eq69 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq9 eq40 -- superposition 40,9, 9 into 40, unify on (0).2 in 9 and (0).1.1.1 in 40
  have eq87 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X1)) := superpose eq40 eq9 -- superposition 9,40, 40 into 9, unify on (0).2 in 40 and (0).1.2.2 in 9
  have eq141 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).1.2 in 42
  have eq147 (X1 X2 : G) : (X2 ◇ X2) = ((X2 ◇ X2) ◇ X1) := superpose eq17 eq42 -- superposition 42,17, 17 into 42, unify on (0).2 in 17 and (0).1.2 in 42
  have eq174 (X0 X1 X2 X3 X5 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X2) = (((X1 ◇ X1) ◇ X1) ◇ ((X5 ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1)))) := superpose eq141 eq25 -- backward demodulation 25,141
  have eq179 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK2) := superpose eq141 eq10 -- backward demodulation 10,141
  have eq187 (X0 X1 X2 X3 X5 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X2) = ((X1 ◇ X1) ◇ ((X5 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1)))) := superpose eq147 eq174 -- backward demodulation 174,147
  have eq195 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq147 eq179 -- backward demodulation 179,147
  have eq197 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X2) = (X1 ◇ X1) := superpose eq147 eq187 -- forward demodulation 187,147
  have eq203 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq197 eq35 -- backward demodulation 35,197
  have eq212 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = (X0 ◇ X0) := superpose eq147 eq203 -- forward demodulation 203,147
  have eq213 (X1 X2 X3 : G) : ((X3 ◇ X3) ◇ (X1 ◇ X2)) = X3 := superpose eq212 eq40 -- backward demodulation 40,212
  have eq228 (X1 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X1))) = (((X4 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ X3) ◇ ((X5 ◇ ((X4 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ X3)) ◇ (X1 ◇ X1))) := superpose eq212 eq24 -- backward demodulation 24,212
  have eq260 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = X2 := superpose eq213 eq69 -- backward demodulation 69,213
  have eq262 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X1)) = X0 := superpose eq260 eq87 -- backward demodulation 87,260
  have eq275 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X1))) = X3 := superpose eq262 eq228 -- forward demodulation 228,262
  have eq277 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq275 eq42 -- backward demodulation 42,275
  have eq283 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq277 eq141 -- backward demodulation 141,277
  have eq291 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X1)) = X3 := superpose eq283 eq275 -- backward demodulation 275,283
  have eq305 (X1 X2 X3 : G) : (X2 ◇ X1) = X3 := superpose eq283 eq291 -- forward demodulation 291,283
  subsumption eq195 eq305


@[equational_result]
theorem Equation964_implies_Equation1594 (G : Type*) [Magma G] (h : Equation964 G) : Equation1594 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = (X0 ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq28 (X0 : G) : sK0 ≠ (sK2 ◇ ((X0 ◇ sK2) ◇ (sK2 ◇ sK0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq28 eq9


@[equational_result]
theorem Equation977_implies_Equation94 (G : Type*) [Magma G] (h : Equation977 G) : Equation94 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq11


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
theorem Equation979_implies_Equation2945 (G : Type*) [Magma G] (h : Equation979 G) : Equation2945 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK0)) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 : G) : (X2 ◇ X3) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq26 (X0 : G) : sK0 ≠ (((sK1 ◇ (X0 ◇ X0)) ◇ sK2) ◇ sK3) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1.2 in 10
  subsumption eq26 eq16


@[equational_result]
theorem Equation985_implies_Equation1014 (G : Type*) [Magma G] (h : Equation985 G) : Equation1014 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ (sK4 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X0 ◇ X1))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq25 (X0 : G) : sK0 ≠ (X0 ◇ ((sK2 ◇ sK3) ◇ (sK4 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq25 eq24


@[equational_result]
theorem Equation989_implies_Equation744 (G : Type*) [Magma G] (h : Equation989 G) : Equation744 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK0 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq11 (X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ (X4 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X2 X3 X4 : G) : (X2 ◇ X3) = (X4 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (X0 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.2 in 10
  subsumption eq23 eq11


@[equational_result]
theorem Equation999_implies_Equation86 (G : Type*) [Magma G] (h : Equation999 G) : Equation86 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : (X4 ◇ (X3 ◇ (X4 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


