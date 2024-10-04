import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation2536_implies_Equation2449 (G : Type*) [Magma G] (h : Equation2536 G) : Equation2449 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ (X1 ◇ X4)) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1.2.1 in 11
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq68 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).1 in 21
  have eq74 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq224 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq74 eq68 -- superposition 68,74, 74 into 68, unify on (0).2 in 74 and (0).1.1.1 in 68
  have eq246 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq224 -- forward demodulation 224,12
  have eq345 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ X1) = ((((X2 ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X1) ◇ X4)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq246 eq13 -- superposition 13,246, 246 into 13, unify on (0).2 in 246 and (0).1.1.1.2 in 13
  have eq355 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq246 eq9 -- superposition 9,246, 246 into 9, unify on (0).2 in 246 and (0).1.1.2 in 9
  have eq364 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq74 eq355 -- forward demodulation 355,74
  have eq370 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq364 eq246 -- backward demodulation 246,364
  have eq375 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X4)) ◇ X1) = X1 := superpose eq364 eq345 -- backward demodulation 345,364
  have eq409 (X0 X1 X4 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X4)) ◇ X1) = X1 := superpose eq370 eq375 -- forward demodulation 375,370
  have eq410 (X1 X4 : G) : ((X1 ◇ X4) ◇ X1) = X1 := superpose eq364 eq409 -- forward demodulation 409,364
  have eq705 : sK0 ≠ sK0 := superpose eq410 eq10 -- superposition 10,410, 410 into 10, unify on (0).2 in 410 and (0).2 in 10
  subsumption eq705 rfl


@[equational_result]
theorem Equation2536_implies_Equation4090 (G : Type*) [Magma G] (h : Equation2536 G) : Equation4090 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.1.2.1 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq340 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.1.2 in 9
  have eq363 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq68 eq340 -- forward demodulation 340,68
  have eq391 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq363 eq10 -- backward demodulation 10,363
  subsumption eq391 rfl


@[equational_result]
theorem Equation2536_implies_Equation3659 (G : Type*) [Magma G] (h : Equation2536 G) : Equation3659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq15 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1.1.2 in 10
  have eq20 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq8 eq15 -- forward demodulation 15,8
  have eq54 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).1.1 in 10
  have eq67 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq54 eq20 -- superposition 20,54, 54 into 20, unify on (0).2 in 54 and (0).2.1.2 in 20
  have eq124 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq67 eq9 -- superposition 9,67, 67 into 9, unify on (0).2 in 67 and (0).2 in 9
  subsumption eq124 rfl


@[equational_result]
theorem Equation2536_implies_Equation1724 (G : Type*) [Magma G] (h : Equation2536 G) : Equation1724 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq70 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq55 eq11 -- superposition 11,55, 55 into 11, unify on (0).2 in 55 and (0).1.1.1.2 in 11
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.1.2.1 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq340 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.1.2 in 9
  have eq363 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq68 eq340 -- forward demodulation 340,68
  have eq373 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq363 eq70 -- backward demodulation 70,363
  have eq394 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq373 eq10 -- backward demodulation 10,373
  subsumption eq394 eq363


@[equational_result]
theorem Equation2536_implies_Equation2733 (G : Type*) [Magma G] (h : Equation2536 G) : Equation2733 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq70 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq55 eq11 -- superposition 11,55, 55 into 11, unify on (0).2 in 55 and (0).1.1.1.2 in 11
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.1.2.1 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq340 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.1.2 in 9
  have eq363 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq68 eq340 -- forward demodulation 340,68
  have eq373 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq363 eq70 -- backward demodulation 70,363
  have eq391 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq363 eq10 -- backward demodulation 10,363
  subsumption eq391 eq373


@[equational_result]
theorem Equation2536_implies_Equation2290 (G : Type*) [Magma G] (h : Equation2536 G) : Equation2290 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1.2 in 11
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq19 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X1 ◇ X3)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq22 (X1 X3 : G) : (X1 ◇ X3) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq23 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq22 eq10 -- backward demodulation 10,22
  have eq56 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq111 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq56 eq21 -- superposition 21,56, 56 into 21, unify on (0).2 in 56 and (0).2.1.2 in 21
  have eq294 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq111 eq15 -- superposition 15,111, 111 into 15, unify on (0).2 in 111 and (0).1 in 15
  have eq318 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq294 -- forward demodulation 294,12
  have eq434 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq318 eq9 -- superposition 9,318, 318 into 9, unify on (0).2 in 318 and (0).1.1.2 in 9
  have eq461 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq111 eq434 -- forward demodulation 434,111
  have eq467 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq461 eq318 -- backward demodulation 318,461
  have eq503 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq467 eq23 -- backward demodulation 23,467
  subsumption eq503 eq56


@[equational_result]
theorem Equation2536_implies_Equation3684 (G : Type*) [Magma G] (h : Equation2536 G) : Equation3684 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.1.2.1 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq340 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.1.2 in 9
  have eq363 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq68 eq340 -- forward demodulation 340,68
  have eq644 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq363 eq10 -- superposition 10,363, 363 into 10, unify on (0).2 in 363 and (0).2 in 10
  subsumption eq644 rfl


@[equational_result]
theorem Equation2536_implies_Equation3464 (G : Type*) [Magma G] (h : Equation2536 G) : Equation3464 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.1.2.1 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq340 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.1.2 in 9
  have eq363 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq68 eq340 -- forward demodulation 340,68
  have eq386 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq363 eq10 -- backward demodulation 10,363
  subsumption eq386 rfl


@[equational_result]
theorem Equation2536_implies_Equation2712 (G : Type*) [Magma G] (h : Equation2536 G) : Equation2712 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq46 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.1.2 in 21
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq64 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) = (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3))) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.1.2.1 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq340 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.1.2 in 9
  have eq363 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq68 eq340 -- forward demodulation 340,68
  have eq1497 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq64 eq9 -- superposition 9,64, 64 into 9, unify on (0).2 in 64 and (0).1.1 in 9
  have eq1554 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) = X1 := superpose eq363 eq1497 -- forward demodulation 1497,363
  have eq1634 : sK0 ≠ sK0 := superpose eq1554 eq10 -- superposition 10,1554, 1554 into 10, unify on (0).2 in 1554 and (0).2 in 10
  subsumption eq1634 rfl


@[equational_result]
theorem Equation2536_implies_Equation3537 (G : Type*) [Magma G] (h : Equation2536 G) : Equation3537 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.1.2.1 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq340 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.1.2 in 9
  have eq363 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq68 eq340 -- forward demodulation 340,68
  have eq386 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq363 eq10 -- backward demodulation 10,363
  subsumption eq386 rfl


@[equational_result]
theorem Equation2536_implies_Equation3664 (G : Type*) [Magma G] (h : Equation2536 G) : Equation3664 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.1.2.1 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq340 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.1.2 in 9
  have eq363 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq68 eq340 -- forward demodulation 340,68
  have eq366 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq363 eq144 -- backward demodulation 144,363
  have eq850 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq366 eq10 -- superposition 10,366, 366 into 10, unify on (0).2 in 366 and (0).2 in 10
  subsumption eq850 rfl


@[equational_result]
theorem Equation2536_implies_Equation3759 (G : Type*) [Magma G] (h : Equation2536 G) : Equation3759 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq68 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).1 in 21
  have eq74 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq224 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq74 eq68 -- superposition 68,74, 74 into 68, unify on (0).2 in 74 and (0).1.1.1 in 68
  have eq246 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq224 -- forward demodulation 224,12
  have eq355 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq246 eq9 -- superposition 9,246, 246 into 9, unify on (0).2 in 246 and (0).1.1.2 in 9
  have eq364 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq74 eq355 -- forward demodulation 355,74
  have eq538 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq364 eq10 -- superposition 10,364, 364 into 10, unify on (0).2 in 364 and (0).2 in 10
  subsumption eq538 rfl


@[equational_result]
theorem Equation2536_implies_Equation1672 (G : Type*) [Magma G] (h : Equation2536 G) : Equation1672 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq70 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq55 eq11 -- superposition 11,55, 55 into 11, unify on (0).2 in 55 and (0).1.1.1.2 in 11
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.1.2.1 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq340 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.1.2 in 9
  have eq363 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq68 eq340 -- forward demodulation 340,68
  have eq373 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq363 eq70 -- backward demodulation 70,363
  have eq391 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq363 eq10 -- backward demodulation 10,363
  subsumption eq391 eq373


@[equational_result]
theorem Equation2536_implies_Equation3519 (G : Type*) [Magma G] (h : Equation2536 G) : Equation3519 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq70 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq55 eq11 -- superposition 11,55, 55 into 11, unify on (0).2 in 55 and (0).1.1.1.2 in 11
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.1.2.1 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq340 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.1.2 in 9
  have eq363 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq68 eq340 -- forward demodulation 340,68
  have eq373 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq363 eq70 -- backward demodulation 70,363
  have eq394 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq373 eq10 -- backward demodulation 10,373
  subsumption eq394 rfl


@[equational_result]
theorem Equation2536_implies_Equation3694 (G : Type*) [Magma G] (h : Equation2536 G) : Equation3694 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.1.2.1 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq340 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.1.2 in 9
  have eq363 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq68 eq340 -- forward demodulation 340,68
  have eq366 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq363 eq144 -- backward demodulation 144,363
  have eq882 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq366 eq10 -- superposition 10,366, 366 into 10, unify on (0).2 in 366 and (0).2 in 10
  subsumption eq882 rfl


@[equational_result]
theorem Equation2536_implies_Equation1731 (G : Type*) [Magma G] (h : Equation2536 G) : Equation1731 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1.2 in 11
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq29 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  have eq57 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq112 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq57 eq21 -- superposition 21,57, 57 into 21, unify on (0).2 in 57 and (0).2.1.2 in 21
  have eq295 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq112 eq15 -- superposition 15,112, 112 into 15, unify on (0).2 in 112 and (0).1 in 15
  have eq319 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq295 -- forward demodulation 295,12
  have eq436 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq319 eq9 -- superposition 9,319, 319 into 9, unify on (0).2 in 319 and (0).1.1.2 in 9
  have eq463 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq112 eq436 -- forward demodulation 436,112
  have eq803 : sK0 ≠ sK0 := superpose eq463 eq29 -- superposition 29,463, 463 into 29, unify on (0).2 in 463 and (0).2 in 29
  subsumption eq803 rfl


@[equational_result]
theorem Equation2536_implies_Equation3509 (G : Type*) [Magma G] (h : Equation2536 G) : Equation3509 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.1.2.1 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq340 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.1.2 in 9
  have eq363 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq68 eq340 -- forward demodulation 340,68
  have eq386 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq363 eq10 -- backward demodulation 10,363
  subsumption eq386 rfl


@[equational_result]
theorem Equation2536_implies_Equation3152 (G : Type*) [Magma G] (h : Equation2536 G) : Equation3152 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ (X1 ◇ X4)) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1.2.1 in 11
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq66 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq55 eq10 -- backward demodulation 10,55
  have eq87 (X0 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq21 eq13 -- superposition 13,21, 21 into 13, unify on (0).2 in 21 and (0).1.1.1 in 13
  have eq120 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq289 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq120 eq87 -- superposition 87,120, 120 into 87, unify on (0).2 in 120 and (0).1.1.1 in 87
  have eq314 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq289 -- forward demodulation 289,12
  have eq450 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq314 eq9 -- superposition 9,314, 314 into 9, unify on (0).2 in 314 and (0).1.1.2 in 9
  have eq462 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq120 eq450 -- forward demodulation 450,120
  have eq661 : sK0 ≠ sK0 := superpose eq462 eq66 -- superposition 66,462, 462 into 66, unify on (0).2 in 462 and (0).2 in 66
  subsumption eq661 rfl


@[equational_result]
theorem Equation2536_implies_Equation3078 (G : Type*) [Magma G] (h : Equation2536 G) : Equation3078 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ (X1 ◇ X4)) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1.2.1 in 11
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq46 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.1.2 in 21
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq64 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) = (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3))) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq68 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).1 in 21
  have eq74 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq224 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq74 eq68 -- superposition 68,74, 74 into 68, unify on (0).2 in 74 and (0).1.1.1 in 68
  have eq246 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq224 -- forward demodulation 224,12
  have eq345 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ X1) = ((((X2 ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X1) ◇ X4)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq246 eq13 -- superposition 13,246, 246 into 13, unify on (0).2 in 246 and (0).1.1.1.2 in 13
  have eq355 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq246 eq9 -- superposition 9,246, 246 into 9, unify on (0).2 in 246 and (0).1.1.2 in 9
  have eq364 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq74 eq355 -- forward demodulation 355,74
  have eq370 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq364 eq246 -- backward demodulation 246,364
  have eq375 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X4)) ◇ X1) = X1 := superpose eq364 eq345 -- backward demodulation 345,364
  have eq409 (X0 X1 X4 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X4)) ◇ X1) = X1 := superpose eq370 eq375 -- forward demodulation 375,370
  have eq410 (X1 X4 : G) : ((X1 ◇ X4) ◇ X1) = X1 := superpose eq364 eq409 -- forward demodulation 409,364
  have eq1498 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq64 eq9 -- superposition 9,64, 64 into 9, unify on (0).2 in 64 and (0).1.1 in 9
  have eq1575 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) = X1 := superpose eq364 eq1498 -- forward demodulation 1498,364
  have eq1611 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X2) = X2 := superpose eq410 eq1575 -- superposition 1575,410, 410 into 1575, unify on (0).2 in 410 and (0).1.1.2 in 1575
  have eq1962 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq1611 eq9 -- superposition 9,1611, 1611 into 9, unify on (0).2 in 1611 and (0).1.1.2 in 9
  have eq2381 : sK0 ≠ sK0 := superpose eq1962 eq10 -- superposition 10,1962, 1962 into 10, unify on (0).2 in 1962 and (0).2 in 10
  subsumption eq2381 rfl


@[equational_result]
theorem Equation2536_implies_Equation3105 (G : Type*) [Magma G] (h : Equation2536 G) : Equation3105 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ (X1 ◇ X4)) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1.2.1 in 11
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq46 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.1.2 in 21
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq64 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) = (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3))) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq68 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).1 in 21
  have eq74 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq224 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq74 eq68 -- superposition 68,74, 74 into 68, unify on (0).2 in 74 and (0).1.1.1 in 68
  have eq246 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq224 -- forward demodulation 224,12
  have eq345 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ X1) = ((((X2 ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X1) ◇ X4)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq246 eq13 -- superposition 13,246, 246 into 13, unify on (0).2 in 246 and (0).1.1.1.2 in 13
  have eq355 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq246 eq9 -- superposition 9,246, 246 into 9, unify on (0).2 in 246 and (0).1.1.2 in 9
  have eq364 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq74 eq355 -- forward demodulation 355,74
  have eq370 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq364 eq246 -- backward demodulation 246,364
  have eq375 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X4)) ◇ X1) = X1 := superpose eq364 eq345 -- backward demodulation 345,364
  have eq409 (X0 X1 X4 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X4)) ◇ X1) = X1 := superpose eq370 eq375 -- forward demodulation 375,370
  have eq410 (X1 X4 : G) : ((X1 ◇ X4) ◇ X1) = X1 := superpose eq364 eq409 -- forward demodulation 409,364
  have eq1498 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq64 eq9 -- superposition 9,64, 64 into 9, unify on (0).2 in 64 and (0).1.1 in 9
  have eq1575 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) = X1 := superpose eq364 eq1498 -- forward demodulation 1498,364
  have eq1611 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X2) = X2 := superpose eq410 eq1575 -- superposition 1575,410, 410 into 1575, unify on (0).2 in 410 and (0).1.1.2 in 1575
  have eq1987 : sK0 ≠ sK0 := superpose eq1611 eq10 -- superposition 10,1611, 1611 into 10, unify on (0).2 in 1611 and (0).2 in 10
  subsumption eq1987 rfl


@[equational_result]
theorem Equation2536_implies_Equation3093 (G : Type*) [Magma G] (h : Equation2536 G) : Equation3093 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq46 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.1.2 in 21
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq64 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) = (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3))) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq70 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq55 eq11 -- superposition 11,55, 55 into 11, unify on (0).2 in 55 and (0).1.1.1.2 in 11
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.1.2.1 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq340 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.1.2 in 9
  have eq363 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq68 eq340 -- forward demodulation 340,68
  have eq373 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq363 eq70 -- backward demodulation 70,363
  have eq1497 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq64 eq9 -- superposition 9,64, 64 into 9, unify on (0).2 in 64 and (0).1.1 in 9
  have eq1554 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) = X1 := superpose eq363 eq1497 -- forward demodulation 1497,363
  have eq1590 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X2) = X2 := superpose eq373 eq1554 -- superposition 1554,373, 373 into 1554, unify on (0).2 in 373 and (0).1.1.2 in 1554
  have eq1910 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq1590 eq9 -- superposition 9,1590, 1590 into 9, unify on (0).2 in 1590 and (0).1.1.2 in 9
  have eq2321 : sK0 ≠ sK0 := superpose eq1910 eq10 -- superposition 10,1910, 1910 into 10, unify on (0).2 in 1910 and (0).2 in 10
  subsumption eq2321 rfl


@[equational_result]
theorem Equation2536_implies_Equation2665 (G : Type*) [Magma G] (h : Equation2536 G) : Equation2665 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq76 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq55 eq11 -- superposition 11,55, 55 into 11, unify on (0).2 in 55 and (0).1.1.1.2.1 in 11
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.1.2.1 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq340 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.1.2 in 9
  have eq363 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq68 eq340 -- forward demodulation 340,68
  have eq374 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq363 eq76 -- backward demodulation 76,363
  have eq1106 : sK0 ≠ sK0 := superpose eq374 eq10 -- superposition 10,374, 374 into 10, unify on (0).2 in 374 and (0).2 in 10
  subsumption eq1106 rfl


@[equational_result]
theorem Equation2536_implies_Equation2558 (G : Type*) [Magma G] (h : Equation2536 G) : Equation2558 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK2) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ (X1 ◇ X4)) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1.2.1 in 11
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq46 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.1.2 in 21
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq64 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) = (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3))) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq68 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).1 in 21
  have eq74 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq224 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq74 eq68 -- superposition 68,74, 74 into 68, unify on (0).2 in 74 and (0).1.1.1 in 68
  have eq246 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq224 -- forward demodulation 224,12
  have eq345 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ X1) = ((((X2 ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X1) ◇ X4)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq246 eq13 -- superposition 13,246, 246 into 13, unify on (0).2 in 246 and (0).1.1.1.2 in 13
  have eq355 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq246 eq9 -- superposition 9,246, 246 into 9, unify on (0).2 in 246 and (0).1.1.2 in 9
  have eq364 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq74 eq355 -- forward demodulation 355,74
  have eq370 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq364 eq246 -- backward demodulation 246,364
  have eq375 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X4)) ◇ X1) = X1 := superpose eq364 eq345 -- backward demodulation 345,364
  have eq409 (X0 X1 X4 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X4)) ◇ X1) = X1 := superpose eq370 eq375 -- forward demodulation 375,370
  have eq410 (X1 X4 : G) : ((X1 ◇ X4) ◇ X1) = X1 := superpose eq364 eq409 -- forward demodulation 409,364
  have eq1499 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq64 eq9 -- superposition 9,64, 64 into 9, unify on (0).2 in 64 and (0).1.1 in 9
  have eq1577 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) = X1 := superpose eq364 eq1499 -- forward demodulation 1499,364
  have eq1663 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq1577 eq9 -- superposition 9,1577, 1577 into 9, unify on (0).2 in 1577 and (0).1.1.2 in 9
  have eq2627 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq1663 eq410 -- superposition 410,1663, 1663 into 410, unify on (0).2 in 1663 and (0).1.1 in 410
  have eq4713 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) = X1 := superpose eq2627 eq9 -- superposition 9,2627, 2627 into 9, unify on (0).2 in 2627 and (0).1.1.2 in 9
  have eq5071 : sK0 ≠ sK0 := superpose eq4713 eq10 -- superposition 10,4713, 4713 into 10, unify on (0).2 in 4713 and (0).2 in 10
  subsumption eq5071 rfl


@[equational_result]
theorem Equation2536_implies_Equation3180 (G : Type*) [Magma G] (h : Equation2536 G) : Equation3180 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK2) ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq46 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.1.2 in 21
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq64 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) = (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3))) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq70 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq55 eq11 -- superposition 11,55, 55 into 11, unify on (0).2 in 55 and (0).1.1.1.2 in 11
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.1.2.1 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq340 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.1.2 in 9
  have eq363 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq68 eq340 -- forward demodulation 340,68
  have eq373 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq363 eq70 -- backward demodulation 70,363
  have eq1497 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq64 eq9 -- superposition 9,64, 64 into 9, unify on (0).2 in 64 and (0).1.1 in 9
  have eq1554 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) = X1 := superpose eq363 eq1497 -- forward demodulation 1497,363
  have eq1590 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X2) = X2 := superpose eq373 eq1554 -- superposition 1554,373, 373 into 1554, unify on (0).2 in 373 and (0).1.1.2 in 1554
  have eq1933 : sK0 ≠ sK0 := superpose eq1590 eq10 -- superposition 10,1590, 1590 into 10, unify on (0).2 in 1590 and (0).2 in 10
  subsumption eq1933 rfl


@[equational_result]
theorem Equation1233_implies_Equation3257 (G : Type*) [Magma G] (h : Equation1233 G) : Equation3257 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq13 (X0 X3 : G) : (X0 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq23 : sK0 ≠ sK0 := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  subsumption eq23 rfl


@[equational_result]
theorem Equation1233_implies_Equation1024 (G : Type*) [Magma G] (h : Equation1233 G) : Equation1024 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq13 (X0 X3 : G) : (X0 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK2)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation1233_implies_Equation102 (G : Type*) [Magma G] (h : Equation1233 G) : Equation102 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation2694_implies_Equation2048 (G : Type*) [Magma G] (h : Equation2694 G) : Equation2048 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X3 X4 X5 : G) : (((X4 ◇ X5) ◇ X0) ◇ X3) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X4 : G) : (X0 ◇ X1) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq22 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ X0) ◇ (sK2 ◇ sK2)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq22 eq12


@[equational_result]
theorem Equation1042_implies_Equation444 (G : Type*) [Magma G] (h : Equation1042 G) : Equation444 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq125 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.2 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.2.1 in 20
  have eq197 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq15 eq148 -- superposition 148,15, 15 into 148, unify on (0).2 in 15 and (0).2.2 in 148
  have eq518 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X1 := superpose eq197 eq11 -- superposition 11,197, 197 into 11, unify on (0).2 in 197 and (0).1.2 in 11
  have eq610 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = X0 := superpose eq518 eq12 -- superposition 12,518, 518 into 12, unify on (0).2 in 518 and (0).1 in 12
  have eq634 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq15 eq610 -- forward demodulation 610,15
  have eq635 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq634 eq10 -- backward demodulation 10,634
  subsumption eq635 eq634


@[equational_result]
theorem Equation1042_implies_Equation3721 (G : Type*) [Magma G] (h : Equation1042 G) : Equation3721 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq125 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.2 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.2.1 in 20
  have eq199 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq148 eq10 -- superposition 10,148, 148 into 10, unify on (0).2 in 148 and (0).2 in 10
  subsumption eq199 rfl


@[equational_result]
theorem Equation1042_implies_Equation105 (G : Type*) [Magma G] (h : Equation1042 G) : Equation105 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation1042_implies_Equation1049 (G : Type*) [Magma G] (h : Equation1042 G) : Equation1049 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq21 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1 in 12
  have eq24 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq48 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq15 eq21 -- superposition 21,15, 15 into 21, unify on (0).2 in 15 and (0).1.2 in 21
  have eq55 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq48 eq10 -- backward demodulation 10,48
  have eq151 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq24 eq12 -- superposition 12,24, 24 into 12, unify on (0).2 in 24 and (0).1 in 12
  have eq161 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq15 eq151 -- forward demodulation 151,15
  have eq243 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq15 eq161 -- superposition 161,15, 15 into 161, unify on (0).2 in 15 and (0).2.2 in 161
  have eq565 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X1 := superpose eq243 eq11 -- superposition 11,243, 243 into 11, unify on (0).2 in 243 and (0).1.2 in 11
  have eq702 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = X0 := superpose eq565 eq12 -- superposition 12,565, 565 into 12, unify on (0).2 in 565 and (0).1 in 12
  have eq727 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq15 eq702 -- forward demodulation 702,15
  have eq863 : sK0 ≠ sK0 := superpose eq727 eq55 -- superposition 55,727, 727 into 55, unify on (0).2 in 727 and (0).2 in 55
  subsumption eq863 rfl


@[equational_result]
theorem Equation1042_implies_Equation3915 (G : Type*) [Magma G] (h : Equation1042 G) : Equation3915 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq21 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1 in 12
  have eq48 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq15 eq21 -- superposition 21,15, 15 into 21, unify on (0).2 in 15 and (0).1.2 in 21
  have eq55 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq48 eq10 -- backward demodulation 10,48
  subsumption eq55 rfl


@[equational_result]
theorem Equation1042_implies_Equation3928 (G : Type*) [Magma G] (h : Equation1042 G) : Equation3928 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq125 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.2 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.2.1 in 20
  have eq197 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq15 eq148 -- superposition 148,15, 15 into 148, unify on (0).2 in 15 and (0).2.2 in 148
  have eq518 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X1 := superpose eq197 eq11 -- superposition 11,197, 197 into 11, unify on (0).2 in 197 and (0).1.2 in 11
  have eq610 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = X0 := superpose eq518 eq12 -- superposition 12,518, 518 into 12, unify on (0).2 in 518 and (0).1 in 12
  have eq634 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq15 eq610 -- forward demodulation 610,15
  have eq635 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq634 eq10 -- backward demodulation 10,634
  subsumption eq635 rfl


@[equational_result]
theorem Equation1042_implies_Equation3323 (G : Type*) [Magma G] (h : Equation1042 G) : Equation3323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq125 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.2 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.2.1 in 20
  have eq197 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq15 eq148 -- superposition 148,15, 15 into 148, unify on (0).2 in 15 and (0).2.2 in 148
  have eq518 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X1 := superpose eq197 eq11 -- superposition 11,197, 197 into 11, unify on (0).2 in 197 and (0).1.2 in 11
  have eq610 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = X0 := superpose eq518 eq12 -- superposition 12,518, 518 into 12, unify on (0).2 in 518 and (0).1 in 12
  have eq634 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq15 eq610 -- forward demodulation 610,15
  have eq635 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq634 eq10 -- backward demodulation 10,634
  subsumption eq635 rfl


@[equational_result]
theorem Equation1042_implies_Equation823 (G : Type*) [Magma G] (h : Equation1042 G) : Equation823 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq125 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.2 in 20
  have eq148 : sK0 ≠ sK0 := superpose eq125 eq10 -- superposition 10,125, 125 into 10, unify on (0).2 in 125 and (0).2 in 10
  subsumption eq148 rfl


@[equational_result]
theorem Equation1042_implies_Equation3862 (G : Type*) [Magma G] (h : Equation1042 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X3)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.2 in 8
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2.1 in 8
  have eq20 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).1 in 11
  have eq47 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq14 eq20 -- superposition 20,14, 14 into 20, unify on (0).2 in 14 and (0).1.2 in 20
  have eq54 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq47 eq9 -- backward demodulation 9,47
  subsumption eq54 rfl


@[equational_result]
theorem Equation1042_implies_Equation3729 (G : Type*) [Magma G] (h : Equation1042 G) : Equation3729 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq125 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.2 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.2.1 in 20
  have eq197 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq15 eq148 -- superposition 148,15, 15 into 148, unify on (0).2 in 15 and (0).2.2 in 148
  have eq518 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X1 := superpose eq197 eq11 -- superposition 11,197, 197 into 11, unify on (0).2 in 197 and (0).1.2 in 11
  have eq610 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = X0 := superpose eq518 eq12 -- superposition 12,518, 518 into 12, unify on (0).2 in 518 and (0).1 in 12
  have eq634 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq15 eq610 -- forward demodulation 610,15
  have eq745 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq634 eq10 -- superposition 10,634, 634 into 10, unify on (0).2 in 634 and (0).2 in 10
  subsumption eq745 rfl


@[equational_result]
theorem Equation1042_implies_Equation843 (G : Type*) [Magma G] (h : Equation1042 G) : Equation843 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq125 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.2 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.2.1 in 20
  have eq197 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq15 eq148 -- superposition 148,15, 15 into 148, unify on (0).2 in 15 and (0).2.2 in 148
  have eq520 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X1 := superpose eq197 eq9 -- superposition 9,197, 197 into 9, unify on (0).2 in 197 and (0).1.2 in 9
  have eq892 : sK0 ≠ sK0 := superpose eq520 eq10 -- superposition 10,520, 520 into 10, unify on (0).2 in 520 and (0).2 in 10
  subsumption eq892 rfl


@[equational_result]
theorem Equation1042_implies_Equation818 (G : Type*) [Magma G] (h : Equation1042 G) : Equation818 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq23 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq73 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq73 rfl


@[equational_result]
theorem Equation1042_implies_Equation844 (G : Type*) [Magma G] (h : Equation1042 G) : Equation844 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq125 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.2 in 20
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq125 eq20 -- superposition 20,125, 125 into 20, unify on (0).2 in 125 and (0).1.2.1 in 20
  have eq197 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq15 eq148 -- superposition 148,15, 15 into 148, unify on (0).2 in 15 and (0).2.2 in 148
  have eq515 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X1 := superpose eq197 eq9 -- superposition 9,197, 197 into 9, unify on (0).2 in 197 and (0).1.2 in 9
  have eq920 : sK0 ≠ sK0 := superpose eq515 eq10 -- superposition 10,515, 515 into 10, unify on (0).2 in 515 and (0).2 in 10
  subsumption eq920 rfl


@[equational_result]
theorem Equation3099_implies_Equation3051 (G : Type*) [Magma G] (h : Equation3099 G) : Equation3051 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq24 (X0 : G) : sK0 ≠ ((((sK0 ◇ X0) ◇ sK0) ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1.1 in 10
  subsumption eq24 eq14


@[equational_result]
theorem Equation3099_implies_Equation3092 (G : Type*) [Magma G] (h : Equation3099 G) : Equation3092 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK1) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq20 (X0 : G) : sK0 ≠ ((((sK0 ◇ X0) ◇ sK2) ◇ sK1) ◇ sK3) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1.1 in 10
  subsumption eq20 eq14


@[equational_result]
theorem Equation68_implies_Equation825 (G : Type*) [Magma G] (h : Equation68 G) : Equation825 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq22 (X0 : G) : sK0 ≠ (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq22 eq20


@[equational_result]
theorem Equation68_implies_Equation791 (G : Type*) [Magma G] (h : Equation68 G) : Equation791 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK3 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq22 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (X0 ◇ sK0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2.2 in 10
  subsumption eq22 eq20


@[equational_result]
theorem Equation1450_implies_Equation2463 (G : Type*) [Magma G] (h : Equation1450 G) : Equation2463 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X4) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq32 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq24 eq10 -- backward demodulation 10,24
  have eq56 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq12 eq24 -- superposition 24,12, 12 into 24, unify on (0).2 in 12 and (0).2 in 24
  have eq83 (X0 : G) : sK0 ≠ ((sK0 ◇ X0) ◇ sK1) := superpose eq24 eq32 -- superposition 32,24, 24 into 32, unify on (0).2 in 24 and (0).2.1 in 32
  subsumption eq83 eq56


@[equational_result]
theorem Equation1450_implies_Equation2259 (G : Type*) [Magma G] (h : Equation1450 G) : Equation2259 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X4) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq32 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq24 eq10 -- backward demodulation 10,24
  have eq56 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq12 eq24 -- superposition 24,12, 12 into 24, unify on (0).2 in 12 and (0).2 in 24
  have eq83 (X0 : G) : sK0 ≠ ((sK0 ◇ X0) ◇ sK0) := superpose eq24 eq32 -- superposition 32,24, 24 into 32, unify on (0).2 in 24 and (0).2.1 in 32
  subsumption eq83 eq56


@[equational_result]
theorem Equation1450_implies_Equation1865 (G : Type*) [Magma G] (h : Equation1450 G) : Equation1865 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X4) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq32 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK2 ◇ sK2)) := superpose eq24 eq10 -- backward demodulation 10,24
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq12 eq24 -- superposition 24,12, 12 into 24, unify on (0).2 in 12 and (0).2 in 24
  have eq59 (X0 : G) : sK0 ≠ ((sK0 ◇ X0) ◇ (sK2 ◇ sK2)) := superpose eq24 eq32 -- superposition 32,24, 24 into 32, unify on (0).2 in 24 and (0).2.1 in 32
  subsumption eq59 eq36


@[equational_result]
theorem Equation1450_implies_Equation4121 (G : Type*) [Magma G] (h : Equation1450 G) : Equation4121 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X4) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq32 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq24 eq10 -- backward demodulation 10,24
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq12 eq24 -- superposition 24,12, 12 into 24, unify on (0).2 in 12 and (0).2 in 24
  have eq59 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq36 eq32 -- backward demodulation 32,36
  subsumption eq59 eq24


@[equational_result]
theorem Equation1450_implies_Equation2282 (G : Type*) [Magma G] (h : Equation1450 G) : Equation2282 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK1) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X4) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq32 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq24 eq10 -- backward demodulation 10,24
  have eq56 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq12 eq24 -- superposition 24,12, 12 into 24, unify on (0).2 in 12 and (0).2 in 24
  have eq83 (X0 : G) : sK0 ≠ ((sK0 ◇ X0) ◇ sK1) := superpose eq24 eq32 -- superposition 32,24, 24 into 32, unify on (0).2 in 24 and (0).2.1 in 32
  subsumption eq83 eq56


@[equational_result]
theorem Equation1450_implies_Equation3092 (G : Type*) [Magma G] (h : Equation1450 G) : Equation3092 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK1) ◇ sK3) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X4) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq32 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK2) ◇ sK1) ◇ sK3) := superpose eq24 eq10 -- backward demodulation 10,24
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq12 eq24 -- superposition 24,12, 12 into 24, unify on (0).2 in 12 and (0).2 in 24
  have eq59 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK3) := superpose eq36 eq32 -- backward demodulation 32,36
  subsumption eq59 eq36


@[equational_result]
theorem Equation2057_implies_Equation2682 (G : Type*) [Magma G] (h : Equation2057 G) : Equation2682 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X3 ◇ (X2 ◇ X1)) ◇ X3) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2 in 12
  have eq27 (X0 X3 X4 : G) : (((X3 ◇ X0) ◇ X3) ◇ X4) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1.2 in 13
  have eq67 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ X0) ◇ sK3) := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2.1 in 10
  have eq260 : sK0 ≠ sK0 := superpose eq27 eq67 -- superposition 67,27, 27 into 67, unify on (0).2 in 27 and (0).2 in 67
  subsumption eq260 rfl


@[equational_result]
theorem Equation3967_implies_Equation3561 (G : Type*) [Magma G] (h : Equation3967 G) : Equation3561 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X1 ◇ X2)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X1))) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 X4 : G) : (((X4 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3) = (X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.2 in 13
  have eq19 (X0 X1 X2 X3 X4 X5 : G) : (((X5 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X4) = (X4 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ (X1 ◇ (X1 ◇ X3)))) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq24 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ (X2 ◇ X4))) = (((X2 ◇ X0) ◇ X2) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1.1 in 13
  have eq27 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3))) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq28 (X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X4))) = ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.1 in 13
  have eq34 (X0 X1 X3 X4 : G) : (X4 ◇ X0) = ((X0 ◇ (((X3 ◇ X1) ◇ X1) ◇ X0)) ◇ X4) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2.1.2 in 9
  have eq37 (X0 X1 X2 X3 X4 : G) : (((X4 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3) = (X3 ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq9 eq15 -- forward demodulation 15,9
  have eq42 (X1 X3 X4 : G) : (X3 ◇ X1) = (X3 ◇ (X1 ◇ (X1 ◇ X4))) := superpose eq9 eq28 -- forward demodulation 28,9
  have eq43 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X2) ◇ X3) = (X3 ◇ X2) := superpose eq42 eq24 -- backward demodulation 24,42
  have eq45 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X2 ◇ X0) ◇ X0)) = (((X4 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3) := superpose eq42 eq37 -- backward demodulation 37,42
  have eq46 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X0) ◇ X3) = (X3 ◇ X0) := superpose eq42 eq13 -- backward demodulation 13,42
  have eq47 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq42 eq27 -- backward demodulation 27,42
  have eq49 (X0 X1 X2 X4 X5 : G) : (((X5 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X4) = (X4 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X1)) := superpose eq42 eq19 -- backward demodulation 19,42
  have eq50 (X0 X2 X3 X4 : G) : (((X4 ◇ X0) ◇ X0) ◇ X3) = (X3 ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq42 eq45 -- forward demodulation 45,42
  have eq54 (X0 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq46 eq50 -- backward demodulation 50,46
  have eq60 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq43 eq47 -- forward demodulation 47,43
  have eq61 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq60 eq9 -- backward demodulation 9,60
  have eq69 (X0 X1 X2 X4 X5 : G) : (((X5 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X4) = (X4 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq46 eq49 -- forward demodulation 49,46
  have eq70 (X0 X1 X4 X5 : G) : (((X5 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X4) = (X4 ◇ X1) := superpose eq54 eq69 -- forward demodulation 69,54
  have eq71 (X0 X1 X4 X5 : G) : (X4 ◇ X1) = (((X5 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X4) := superpose eq60 eq70 -- forward demodulation 70,60
  have eq72 (X0 X1 X4 X5 : G) : (X4 ◇ X1) = (((X5 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ X4) := superpose eq60 eq71 -- forward demodulation 71,60
  have eq73 (X0 X1 X4 X5 : G) : (X4 ◇ X1) = (((X5 ◇ (X0 ◇ X1)) ◇ X0) ◇ X4) := superpose eq60 eq72 -- forward demodulation 72,60
  have eq74 (X0 X1 X4 X5 : G) : (((X5 ◇ X0) ◇ X0) ◇ X4) = (X4 ◇ X1) := superpose eq60 eq73 -- forward demodulation 73,60
  have eq85 (X0 X1 X3 X4 : G) : (X4 ◇ X0) = ((X0 ◇ ((X3 ◇ X1) ◇ X1)) ◇ X4) := superpose eq60 eq34 -- forward demodulation 34,60
  have eq86 (X0 X1 X3 X4 : G) : (X4 ◇ X0) = ((X0 ◇ (X3 ◇ X1)) ◇ X4) := superpose eq60 eq85 -- forward demodulation 85,60
  have eq87 (X0 X3 X4 : G) : (X4 ◇ X0) = ((X0 ◇ X3) ◇ X4) := superpose eq60 eq86 -- forward demodulation 86,60
  have eq93 (X0 X1 X4 X5 : G) : (X4 ◇ X1) = ((X0 ◇ X5) ◇ X4) := superpose eq87 eq74 -- backward demodulation 74,87
  have eq95 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq87 eq10 -- backward demodulation 10,87
  have eq145 (X0 X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ X0) := superpose eq61 eq93 -- superposition 93,61, 61 into 93, unify on (0).2 in 61 and (0).2 in 93
  have eq168 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X0 ◇ X1) ◇ X4) := superpose eq93 eq145 -- superposition 145,93, 93 into 145, unify on (0).2 in 93 and (0).1 in 145
  have eq195 (X0 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ X0) := superpose eq145 eq95 -- superposition 95,145, 145 into 95, unify on (0).2 in 145 and (0).2 in 95
  have eq253 (X1 X2 : G) : (sK0 ◇ sK1) ≠ ((X1 ◇ X2) ◇ sK1) := superpose eq93 eq195 -- superposition 195,93, 93 into 195, unify on (0).2 in 93 and (0).2 in 195
  subsumption eq253 eq168


@[equational_result]
theorem Equation3505_implies_Equation3484 (G : Type*) [Magma G] (h : Equation3505 G) : Equation3484 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X3) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq14 (X0 X3 X4 X5 : G) : (X4 ◇ X4) = (X5 ◇ ((X3 ◇ X3) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ ((X0 ◇ X0) ◇ sK0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2.1 in 10
  subsumption eq26 eq14


@[equational_result]
theorem Equation3505_implies_Equation3473 (G : Type*) [Magma G] (h : Equation3505 G) : Equation3473 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X3) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq14 (X0 X3 X4 X5 : G) : (X4 ◇ X4) = (X5 ◇ ((X3 ◇ X3) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq29 (X0 : G) : (X0 ◇ X0) ≠ (sK1 ◇ ((X0 ◇ X0) ◇ sK2)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).1 in 10
  subsumption eq29 eq14


@[equational_result]
theorem Equation3349_implies_Equation4112 (G : Type*) [Magma G] (h : Equation3349 G) : Equation4112 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK3) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq518 : (sK0 ◇ sK0) ≠ ((sK3 ◇ sK3) ◇ sK0) := superpose eq486 eq10 -- backward demodulation 10,486
  subsumption eq518 eq486


@[equational_result]
theorem Equation3349_implies_Equation4243 (G : Type*) [Magma G] (h : Equation3349 G) : Equation4243 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK3) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq487 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq263 eq348 -- superposition 348,263, 263 into 348, unify on (0).2 in 263 and (0).2 in 348
  have eq518 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq486 eq10 -- backward demodulation 10,486
  have eq588 (X0 : G) : (sK0 ◇ sK1) ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq486 eq518 -- superposition 518,486, 486 into 518, unify on (0).2 in 486 and (0).2.1 in 518
  subsumption eq588 eq487


@[equational_result]
theorem Equation3349_implies_Equation4316 (G : Type*) [Magma G] (h : Equation3349 G) : Equation4316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq221 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ X1)) := superpose eq12 eq122 -- superposition 122,12, 12 into 122, unify on (0).2 in 12 and (0).2 in 122
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq518 : (sK0 ◇ (sK2 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq486 eq10 -- backward demodulation 10,486
  subsumption eq518 eq221


@[equational_result]
theorem Equation3349_implies_Equation4677 (G : Type*) [Magma G] (h : Equation3349 G) : Equation4677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK1 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq518 : ((sK0 ◇ sK1) ◇ sK2) ≠ (sK2 ◇ sK2) := superpose eq486 eq10 -- backward demodulation 10,486
  subsumption eq518 eq486


@[equational_result]
theorem Equation3349_implies_Equation4086 (G : Type*) [Magma G] (h : Equation3349 G) : Equation4086 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK0) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq518 : (sK0 ◇ sK0) ≠ ((sK2 ◇ sK2) ◇ sK0) := superpose eq486 eq10 -- backward demodulation 10,486
  subsumption eq518 eq486


@[equational_result]
theorem Equation3349_implies_Equation4296 (G : Type*) [Magma G] (h : Equation3349 G) : Equation4296 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq156 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq32 eq11 -- superposition 11,32, 32 into 11, unify on (0).2 in 32 and (0).2.2 in 11
  have eq171 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X3 ◇ (X1 ◇ X2)))) = ((X1 ◇ (X3 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq32 eq11 -- superposition 11,32, 32 into 11, unify on (0).2 in 32 and (0).2.2 in 11
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq197 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq9 eq156 -- forward demodulation 156,9
  have eq201 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X3 ◇ (X1 ◇ X2)))) := superpose eq197 eq171 -- forward demodulation 171,197
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq302 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X2)) := superpose eq301 eq201 -- backward demodulation 201,301
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq518 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq486 eq10 -- backward demodulation 10,486
  subsumption eq518 eq302


@[equational_result]
theorem Equation3349_implies_Equation3326 (G : Type*) [Magma G] (h : Equation3349 G) : Equation3326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq515 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq348 eq10 -- superposition 10,348, 348 into 10, unify on (0).2 in 348 and (0).2 in 10
  subsumption eq515 rfl


@[equational_result]
theorem Equation3349_implies_Equation3451 (G : Type*) [Magma G] (h : Equation3349 G) : Equation3451 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq487 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq263 eq348 -- superposition 348,263, 263 into 348, unify on (0).2 in 263 and (0).2 in 348
  have eq515 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK1) := superpose eq348 eq10 -- superposition 10,348, 348 into 10, unify on (0).2 in 348 and (0).2 in 10
  subsumption eq515 eq487


@[equational_result]
theorem Equation3349_implies_Equation4599 (G : Type*) [Magma G] (h : Equation3349 G) : Equation4599 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq20 : ((sK0 ◇ sK0) ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq27 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq29 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq27 -- forward demodulation 27,9
  have eq30 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq29 -- forward demodulation 29,19
  have eq41 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq47 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq66 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).1.1 in 30
  have eq83 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq66 -- forward demodulation 66,12
  have eq154 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq83 eq11 -- superposition 11,83, 83 into 11, unify on (0).2 in 83 and (0).2.2 in 11
  have eq178 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq154 -- forward demodulation 154,11
  have eq179 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq178 -- forward demodulation 178,9
  have eq185 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq179 eq47 -- backward demodulation 47,179
  have eq227 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq185 eq185 -- superposition 185,185, 185 into 185, unify on (0).2 in 185 and (0).1 in 185
  have eq265 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X1 ◇ X2))) := superpose eq227 eq41 -- backward demodulation 41,227
  have eq288 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ X2) = (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) := superpose eq227 eq265 -- forward demodulation 265,227
  have eq289 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X2) = (X4 ◇ (X3 ◇ (X0 ◇ X2))) := superpose eq227 eq288 -- forward demodulation 288,227
  have eq324 (X0 X1 X3 : G) : (X1 ◇ X0) = (X3 ◇ X0) := superpose eq9 eq289 -- superposition 289,9, 9 into 289, unify on (0).2 in 9 and (0).2 in 289
  have eq504 (X0 : G) : (sK1 ◇ sK1) ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq324 eq20 -- superposition 20,324, 324 into 20, unify on (0).2 in 324 and (0).1.1 in 20
  subsumption eq504 eq324


@[equational_result]
theorem Equation3349_implies_Equation3864 (G : Type*) [Magma G] (h : Equation3349 G) : Equation3864 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq565 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq486 eq10 -- superposition 10,486, 486 into 10, unify on (0).2 in 486 and (0).2 in 10
  subsumption eq565 rfl


@[equational_result]
theorem Equation3349_implies_Equation4320 (G : Type*) [Magma G] (h : Equation3349 G) : Equation4320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq156 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq32 eq11 -- superposition 11,32, 32 into 11, unify on (0).2 in 32 and (0).2.2 in 11
  have eq171 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X3 ◇ (X1 ◇ X2)))) = ((X1 ◇ (X3 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq32 eq11 -- superposition 11,32, 32 into 11, unify on (0).2 in 32 and (0).2.2 in 11
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq197 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq9 eq156 -- forward demodulation 156,9
  have eq201 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X3 ◇ (X1 ◇ X2)))) := superpose eq197 eq171 -- forward demodulation 171,197
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq302 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X2)) := superpose eq301 eq201 -- backward demodulation 201,301
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq518 : (sK1 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq486 eq10 -- backward demodulation 10,486
  subsumption eq518 eq302


@[equational_result]
theorem Equation3349_implies_Equation4362 (G : Type*) [Magma G] (h : Equation3349 G) : Equation4362 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq487 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq263 eq348 -- superposition 348,263, 263 into 348, unify on (0).2 in 263 and (0).2 in 348
  have eq499 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X0 ◇ X2)) := superpose eq348 eq263 -- superposition 263,348, 348 into 263, unify on (0).2 in 348 and (0).2.2 in 263
  have eq769 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (X0 ◇ sK2)) := superpose eq487 eq10 -- superposition 10,487, 487 into 10, unify on (0).2 in 487 and (0).2.2 in 10
  subsumption eq769 eq499


@[equational_result]
theorem Equation3349_implies_Equation4611 (G : Type*) [Magma G] (h : Equation3349 G) : Equation4611 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq518 : ((sK0 ◇ sK0) ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq486 eq10 -- backward demodulation 10,486
  subsumption eq518 eq486


@[equational_result]
theorem Equation3349_implies_Equation3258 (G : Type*) [Magma G] (h : Equation3349 G) : Equation3258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq20 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq27 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq20 eq9 -- superposition 9,20, 20 into 9, unify on (0).2 in 20 and (0).2.2 in 9
  have eq29 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq27 -- forward demodulation 27,9
  have eq30 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq20 eq29 -- forward demodulation 29,20
  have eq47 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq66 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).1.1 in 30
  have eq83 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq66 -- forward demodulation 66,12
  have eq154 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq83 eq11 -- superposition 11,83, 83 into 11, unify on (0).2 in 83 and (0).2.2 in 11
  have eq178 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq154 -- forward demodulation 154,11
  have eq179 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq178 -- forward demodulation 178,9
  have eq185 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq179 eq47 -- backward demodulation 47,179
  have eq234 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := superpose eq185 eq185 -- superposition 185,185, 185 into 185, unify on (0).2 in 185 and (0).2.2 in 185
  have eq294 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq234 eq10 -- backward demodulation 10,234
  subsumption eq294 eq9


@[equational_result]
theorem Equation3349_implies_Equation361 (G : Type*) [Magma G] (h : Equation3349 G) : Equation361 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq565 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq486 eq10 -- superposition 10,486, 486 into 10, unify on (0).2 in 486 and (0).2 in 10
  subsumption eq565 rfl


@[equational_result]
theorem Equation3349_implies_Equation4360 (G : Type*) [Magma G] (h : Equation3349 G) : Equation4360 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq18 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X1)) = ((X2 ◇ X1) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq80 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ X1) ◇ (X5 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1)))))) = (((X0 ◇ X1) ◇ (X5 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1))))) ◇ (X4 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq18 eq11 -- superposition 11,18, 18 into 11, unify on (0).2 in 18 and (0).2.2.2 in 11
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq308 (X0 X1 X2 X4 X5 : G) : (X4 ◇ ((X0 ◇ X1) ◇ (X5 ◇ (X1 ◇ X1)))) = (((X0 ◇ X1) ◇ (X5 ◇ (X1 ◇ X1))) ◇ (X4 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq301 eq80 -- backward demodulation 80,301
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq339 (X0 X1 X4 X5 : G) : (X4 ◇ (X0 ◇ X1)) = (X4 ◇ ((X0 ◇ X1) ◇ (X5 ◇ (X1 ◇ X1)))) := superpose eq301 eq308 -- forward demodulation 308,301
  have eq340 (X0 X1 X4 X5 : G) : (X4 ◇ (X0 ◇ X1)) = (X4 ◇ (X5 ◇ X1)) := superpose eq301 eq339 -- forward demodulation 339,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq518 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq486 eq10 -- backward demodulation 10,486
  subsumption eq518 eq340


@[equational_result]
theorem Equation3349_implies_Equation3338 (G : Type*) [Magma G] (h : Equation3349 G) : Equation3338 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq515 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq348 eq10 -- superposition 10,348, 348 into 10, unify on (0).2 in 348 and (0).2 in 10
  subsumption eq515 rfl


@[equational_result]
theorem Equation3349_implies_Equation3877 (G : Type*) [Magma G] (h : Equation3349 G) : Equation3877 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq107 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq58 eq10 -- superposition 10,58, 58 into 10, unify on (0).2 in 58 and (0).2 in 10
  subsumption eq107 rfl


@[equational_result]
theorem Equation3349_implies_Equation3388 (G : Type*) [Magma G] (h : Equation3349 G) : Equation3388 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq519 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) := superpose eq486 eq10 -- backward demodulation 10,486
  subsumption eq519 eq301


@[equational_result]
theorem Equation3349_implies_Equation3943 (G : Type*) [Magma G] (h : Equation3349 G) : Equation3943 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq562 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq486 eq10 -- superposition 10,486, 486 into 10, unify on (0).2 in 486 and (0).2 in 10
  subsumption eq562 eq486


@[equational_result]
theorem Equation3349_implies_Equation3931 (G : Type*) [Magma G] (h : Equation3349 G) : Equation3931 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq562 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq486 eq10 -- superposition 10,486, 486 into 10, unify on (0).2 in 486 and (0).2 in 10
  subsumption eq562 eq486


@[equational_result]
theorem Equation3349_implies_Equation3264 (G : Type*) [Magma G] (h : Equation3349 G) : Equation3264 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq20 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq27 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq20 eq9 -- superposition 9,20, 20 into 9, unify on (0).2 in 20 and (0).2.2 in 9
  have eq29 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq27 -- forward demodulation 27,9
  have eq30 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq20 eq29 -- forward demodulation 29,20
  have eq41 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq47 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq66 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).1.1 in 30
  have eq83 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq66 -- forward demodulation 66,12
  have eq154 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq83 eq11 -- superposition 11,83, 83 into 11, unify on (0).2 in 83 and (0).2.2 in 11
  have eq178 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq154 -- forward demodulation 154,11
  have eq179 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq178 -- forward demodulation 178,9
  have eq185 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq179 eq47 -- backward demodulation 47,179
  have eq227 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq185 eq185 -- superposition 185,185, 185 into 185, unify on (0).2 in 185 and (0).1 in 185
  have eq265 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X1 ◇ X2))) := superpose eq227 eq41 -- backward demodulation 41,227
  have eq288 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ X2) = (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) := superpose eq227 eq265 -- forward demodulation 265,227
  have eq289 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X2) = (X4 ◇ (X3 ◇ (X0 ◇ X2))) := superpose eq227 eq288 -- forward demodulation 288,227
  have eq324 (X0 X1 X3 : G) : (X1 ◇ X0) = (X3 ◇ X0) := superpose eq9 eq289 -- superposition 289,9, 9 into 289, unify on (0).2 in 9 and (0).2 in 289
  have eq366 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq289 eq10 -- superposition 10,289, 289 into 10, unify on (0).2 in 289 and (0).2 in 10
  subsumption eq366 eq324


@[equational_result]
theorem Equation3349_implies_Equation3870 (G : Type*) [Magma G] (h : Equation3349 G) : Equation3870 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq584 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq486 eq10 -- superposition 10,486, 486 into 10, unify on (0).2 in 486 and (0).2 in 10
  subsumption eq584 rfl


@[equational_result]
theorem Equation3349_implies_Equation3890 (G : Type*) [Magma G] (h : Equation3349 G) : Equation3890 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq566 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq486 eq10 -- superposition 10,486, 486 into 10, unify on (0).2 in 486 and (0).2 in 10
  subsumption eq566 rfl


@[equational_result]
theorem Equation3349_implies_Equation4200 (G : Type*) [Magma G] (h : Equation3349 G) : Equation4200 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK0) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq487 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq263 eq348 -- superposition 348,263, 263 into 348, unify on (0).2 in 263 and (0).2 in 348
  have eq518 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ sK1) := superpose eq486 eq10 -- backward demodulation 10,486
  have eq588 (X0 : G) : (sK0 ◇ sK1) ≠ ((X0 ◇ sK2) ◇ sK1) := superpose eq486 eq518 -- superposition 518,486, 486 into 518, unify on (0).2 in 486 and (0).2.1 in 518
  subsumption eq588 eq487


@[equational_result]
theorem Equation3349_implies_Equation370 (G : Type*) [Magma G] (h : Equation3349 G) : Equation370 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq565 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq486 eq10 -- superposition 10,486, 486 into 10, unify on (0).2 in 486 and (0).2 in 10
  subsumption eq565 rfl


@[equational_result]
theorem Equation3349_implies_Equation3921 (G : Type*) [Magma G] (h : Equation3349 G) : Equation3921 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq544 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq486 eq10 -- superposition 10,486, 486 into 10, unify on (0).2 in 486 and (0).2 in 10
  subsumption eq544 eq486


@[equational_result]
theorem Equation3349_implies_Equation3997 (G : Type*) [Magma G] (h : Equation3349 G) : Equation3997 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK0 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq562 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq486 eq10 -- superposition 10,486, 486 into 10, unify on (0).2 in 486 and (0).2 in 10
  subsumption eq562 eq486


@[equational_result]
theorem Equation3349_implies_Equation4693 (G : Type*) [Magma G] (h : Equation3349 G) : Equation4693 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK3 ◇ sK4) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq518 : ((sK0 ◇ sK1) ◇ sK2) ≠ (sK2 ◇ sK2) := superpose eq486 eq10 -- backward demodulation 10,486
  subsumption eq518 eq486


@[equational_result]
theorem Equation3349_implies_Equation3281 (G : Type*) [Magma G] (h : Equation3349 G) : Equation3281 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq18 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X1)) = ((X2 ◇ X1) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq67 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1))))) = ((X5 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1)))) ◇ (X4 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq18 eq18 -- superposition 18,18, 18 into 18, unify on (0).2 in 18 and (0).2.2.2.2 in 18
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq305 (X0 X1 X2 X4 X5 : G) : (X4 ◇ (X5 ◇ (X1 ◇ X1))) = ((X5 ◇ (X1 ◇ X1)) ◇ (X4 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq301 eq67 -- backward demodulation 67,301
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq333 (X0 X1 X4 X5 : G) : (X4 ◇ (X5 ◇ (X1 ◇ X1))) = ((X5 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq301 eq305 -- forward demodulation 305,301
  have eq334 (X1 X4 X5 : G) : (X4 ◇ (X5 ◇ (X1 ◇ X1))) = ((X5 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq12 eq333 -- forward demodulation 333,12
  have eq335 (X1 X4 X5 : G) : (X1 ◇ X1) = (X4 ◇ (X5 ◇ (X1 ◇ X1))) := superpose eq301 eq334 -- forward demodulation 334,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq487 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq520 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq487 eq10 -- backward demodulation 10,487
  subsumption eq520 eq335


@[equational_result]
theorem Equation3349_implies_Equation3261 (G : Type*) [Magma G] (h : Equation3349 G) : Equation3261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq20 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq27 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq20 eq9 -- superposition 9,20, 20 into 9, unify on (0).2 in 20 and (0).2.2 in 9
  have eq29 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq27 -- forward demodulation 27,9
  have eq30 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq20 eq29 -- forward demodulation 29,20
  have eq41 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq47 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq66 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).1.1 in 30
  have eq83 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq66 -- forward demodulation 66,12
  have eq154 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq83 eq11 -- superposition 11,83, 83 into 11, unify on (0).2 in 83 and (0).2.2 in 11
  have eq178 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq154 -- forward demodulation 154,11
  have eq179 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq178 -- forward demodulation 178,9
  have eq185 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq179 eq47 -- backward demodulation 47,179
  have eq227 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq185 eq185 -- superposition 185,185, 185 into 185, unify on (0).2 in 185 and (0).1 in 185
  have eq266 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X1 ◇ X2))) := superpose eq227 eq41 -- backward demodulation 41,227
  have eq289 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ X2) = (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) := superpose eq227 eq266 -- forward demodulation 266,227
  have eq290 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X2) = (X4 ◇ (X3 ◇ (X0 ◇ X2))) := superpose eq227 eq289 -- forward demodulation 289,227
  have eq325 (X0 X1 X3 : G) : (X1 ◇ X0) = (X3 ◇ X0) := superpose eq9 eq290 -- superposition 290,9, 9 into 290, unify on (0).2 in 9 and (0).2 in 290
  have eq367 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq290 eq10 -- superposition 10,290, 290 into 10, unify on (0).2 in 290 and (0).2 in 10
  subsumption eq367 eq325


@[equational_result]
theorem Equation3349_implies_Equation4351 (G : Type*) [Magma G] (h : Equation3349 G) : Equation4351 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq487 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq263 eq348 -- superposition 348,263, 263 into 348, unify on (0).2 in 263 and (0).2 in 348
  have eq583 (X0 : G) : (sK0 ◇ (X0 ◇ sK1)) ≠ (sK2 ◇ (X0 ◇ sK1)) := superpose eq486 eq10 -- superposition 10,486, 486 into 10, unify on (0).2 in 486 and (0).1.2 in 10
  subsumption eq583 eq487


@[equational_result]
theorem Equation3349_implies_Equation381 (G : Type*) [Magma G] (h : Equation3349 G) : Equation381 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq544 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq486 eq10 -- superposition 10,486, 486 into 10, unify on (0).2 in 486 and (0).2 in 10
  subsumption eq544 eq486


@[equational_result]
theorem Equation3349_implies_Equation3867 (G : Type*) [Magma G] (h : Equation3349 G) : Equation3867 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq107 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq58 eq10 -- superposition 10,58, 58 into 10, unify on (0).2 in 58 and (0).2 in 10
  subsumption eq107 rfl


@[equational_result]
theorem Equation3349_implies_Equation4304 (G : Type*) [Magma G] (h : Equation3349 G) : Equation4304 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq156 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq32 eq11 -- superposition 11,32, 32 into 11, unify on (0).2 in 32 and (0).2.2 in 11
  have eq171 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X3 ◇ (X1 ◇ X2)))) = ((X1 ◇ (X3 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq32 eq11 -- superposition 11,32, 32 into 11, unify on (0).2 in 32 and (0).2.2 in 11
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq197 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq9 eq156 -- forward demodulation 156,9
  have eq201 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X3 ◇ (X1 ◇ X2)))) := superpose eq197 eq171 -- forward demodulation 171,197
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq302 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X2)) := superpose eq301 eq201 -- backward demodulation 201,301
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq583 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (X0 ◇ sK1)) := superpose eq486 eq10 -- superposition 10,486, 486 into 10, unify on (0).2 in 486 and (0).2.2 in 10
  subsumption eq583 eq302


@[equational_result]
theorem Equation3349_implies_Equation4307 (G : Type*) [Magma G] (h : Equation3349 G) : Equation4307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq156 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq32 eq11 -- superposition 11,32, 32 into 11, unify on (0).2 in 32 and (0).2.2 in 11
  have eq171 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X3 ◇ (X1 ◇ X2)))) = ((X1 ◇ (X3 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq32 eq11 -- superposition 11,32, 32 into 11, unify on (0).2 in 32 and (0).2.2 in 11
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq197 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq9 eq156 -- forward demodulation 156,9
  have eq201 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X3 ◇ (X1 ◇ X2)))) := superpose eq197 eq171 -- forward demodulation 171,197
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq302 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X2)) := superpose eq301 eq201 -- backward demodulation 201,301
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq518 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK1)) := superpose eq486 eq10 -- backward demodulation 10,486
  subsumption eq518 eq302


@[equational_result]
theorem Equation3349_implies_Equation3928 (G : Type*) [Magma G] (h : Equation3349 G) : Equation3928 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) = ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq18 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X1)) = ((X2 ◇ X1) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2.2 in 9
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq26 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X4 ◇ (X1 ◇ (X2 ◇ X0))))) = ((X0 ◇ (X4 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X3 ◇ (X2 ◇ X0)))) = ((X1 ◇ (X3 ◇ (X2 ◇ X0))) ◇ (X1 ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq30 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq67 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1))))) = ((X5 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1)))) ◇ (X4 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq18 eq18 -- superposition 18,18, 18 into 18, unify on (0).2 in 18 and (0).2.2.2.2 in 18
  have eq73 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) = ((X3 ◇ X2) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq11 eq18 -- superposition 18,11, 11 into 18, unify on (0).2 in 11 and (0).2.2 in 18
  have eq81 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X1 ◇ (X3 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = ((X2 ◇ (X0 ◇ X1)) ◇ (X4 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1))))) := superpose eq18 eq12 -- superposition 12,18, 18 into 12, unify on (0).2 in 18 and (0).1.2 in 12
  have eq88 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) = ((X3 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq9 eq73 -- forward demodulation 73,9
  have eq89 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) := superpose eq12 eq88 -- forward demodulation 88,12
  have eq91 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) := superpose eq89 eq13 -- backward demodulation 13,89
  have eq103 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X3 ◇ X1))) = ((X1 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X3 ◇ X1))) := superpose eq18 eq58 -- superposition 58,18, 18 into 58, unify on (0).2 in 18 and (0).1.1 in 58
  have eq104 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X2)) = ((X0 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq11 eq58 -- superposition 58,11, 11 into 58, unify on (0).2 in 11 and (0).1.1 in 58
  have eq107 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq58 eq10 -- superposition 10,58, 58 into 10, unify on (0).2 in 58 and (0).2 in 10
  have eq124 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X2)) = (X2 ◇ (X0 ◇ X2)) := superpose eq12 eq104 -- forward demodulation 104,12
  have eq127 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) := superpose eq124 eq15 -- backward demodulation 15,124
  have eq139 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2))))) = (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq173 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2)))) = (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq32 eq11 -- superposition 11,32, 32 into 11, unify on (0).2 in 32 and (0).1.2 in 11
  have eq210 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X4 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq32 eq91 -- superposition 91,32, 32 into 91, unify on (0).2 in 32 and (0).1.2 in 91
  have eq241 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq91 -- superposition 91,9, 9 into 91, unify on (0).2 in 9 and (0).2 in 91
  have eq263 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X3 ◇ (X4 ◇ (X0 ◇ X1)))) := superpose eq9 eq210 -- forward demodulation 210,9
  have eq264 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ X1)) = ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X3 ◇ (X4 ◇ (X0 ◇ X1)))) := superpose eq127 eq263 -- forward demodulation 263,127
  have eq265 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = (X3 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq264 eq173 -- backward demodulation 173,264
  have eq267 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X2))) = (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq265 eq139 -- backward demodulation 139,265
  have eq287 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X3 ◇ (X2 ◇ X0)))) := superpose eq241 eq29 -- backward demodulation 29,241
  have eq289 (X0 X1 X3 X4 : G) : (X3 ◇ (X0 ◇ (X4 ◇ X0))) = ((X0 ◇ (X4 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq287 eq26 -- backward demodulation 26,287
  have eq290 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X3 ◇ X1))) = (X1 ◇ (X1 ◇ (X3 ◇ X1))) := superpose eq289 eq103 -- backward demodulation 103,289
  have eq291 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X3 ◇ X1))) := superpose eq9 eq290 -- forward demodulation 290,9
  have eq292 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq291 eq30 -- backward demodulation 30,291
  have eq299 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X2))) = ((X2 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq292 eq267 -- backward demodulation 267,292
  have eq324 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X2))) = (X2 ◇ X2) := superpose eq292 eq299 -- forward demodulation 299,292
  have eq328 (X0 X1 X2 X4 X5 : G) : (X4 ◇ (X5 ◇ (X1 ◇ X1))) = ((X5 ◇ (X1 ◇ X1)) ◇ (X4 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq324 eq67 -- backward demodulation 67,324
  have eq332 (X0 X1 X2 X4 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X4 ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq324 eq81 -- backward demodulation 81,324
  have eq346 (X1 X4 X5 : G) : (X4 ◇ (X5 ◇ (X1 ◇ X1))) = ((X5 ◇ (X1 ◇ X1)) ◇ (X4 ◇ (X1 ◇ X1))) := superpose eq292 eq328 -- forward demodulation 328,292
  have eq349 (X0 X1 X2 X4 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X4 ◇ (X1 ◇ X1))) := superpose eq292 eq332 -- forward demodulation 332,292
  have eq350 (X1 X4 X5 : G) : (X1 ◇ X1) = (X4 ◇ (X5 ◇ (X1 ◇ X1))) := superpose eq349 eq346 -- backward demodulation 346,349
  have eq1310 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq350 -- superposition 350,9, 9 into 350, unify on (0).2 in 9 and (0).2 in 350
  have eq1603 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq1310 eq1310 -- superposition 1310,1310, 1310 into 1310, unify on (0).2 in 1310 and (0).2 in 1310
  have eq1708 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq1310 eq107 -- superposition 107,1310, 1310 into 107, unify on (0).2 in 1310 and (0).2 in 107
  subsumption eq1708 eq1603


@[equational_result]
theorem Equation3349_implies_Equation3268 (G : Type*) [Magma G] (h : Equation3349 G) : Equation3268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq467 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq263 eq10 -- superposition 10,263, 263 into 10, unify on (0).2 in 263 and (0).2 in 10
  subsumption eq467 rfl


@[equational_result]
theorem Equation3349_implies_Equation4327 (G : Type*) [Magma G] (h : Equation3349 G) : Equation4327 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.2 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).1.1 in 58
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq156 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq32 eq11 -- superposition 11,32, 32 into 11, unify on (0).2 in 32 and (0).2.2 in 11
  have eq171 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X3 ◇ (X1 ◇ X2)))) = ((X1 ◇ (X3 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq32 eq11 -- superposition 11,32, 32 into 11, unify on (0).2 in 32 and (0).2.2 in 11
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq142 -- forward demodulation 142,9
  have eq197 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq9 eq156 -- forward demodulation 156,9
  have eq201 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X3 ◇ (X1 ◇ X2)))) := superpose eq197 eq171 -- forward demodulation 171,197
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.2 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq11 eq226 -- forward demodulation 226,11
  have eq262 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq261 -- forward demodulation 261,9
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq262 eq32 -- backward demodulation 32,262
  have eq286 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq263 eq188 -- backward demodulation 188,263
  have eq301 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq262 eq286 -- forward demodulation 286,262
  have eq302 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X2)) := superpose eq301 eq201 -- backward demodulation 201,301
  have eq321 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq301 eq28 -- backward demodulation 28,301
  have eq347 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = (X4 ◇ X2) := superpose eq301 eq321 -- forward demodulation 321,301
  have eq348 (X0 X2 X4 X5 : G) : (X4 ◇ X2) = (X4 ◇ (X5 ◇ (X0 ◇ X2))) := superpose eq301 eq347 -- forward demodulation 347,301
  have eq486 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq348 -- superposition 348,9, 9 into 348, unify on (0).2 in 9 and (0).2 in 348
  have eq518 : (sK2 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq486 eq10 -- backward demodulation 10,486
  subsumption eq518 eq302


