import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation699_implies_Equation1976 (G : Type*) [Magma G] (h : Equation699 G) : Equation1976 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X1 X4 X5 : G) : (X4 ◇ (X5 ◇ (X1 ◇ X4))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ X1) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq17 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq21 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq17 eq16 -- backward demodulation 16,17
  have eq26 (X1 X3 : G) : X1 = X3 := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).1 in 21
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq32 eq26


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
theorem Equation1923_implies_Equation3143 (G : Type*) [Magma G] (h : Equation1923 G) : Equation3143 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X3 X4 : G) : (((X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X4)) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq17 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X3 ◇ (X3 ◇ X0)) ◇ X0) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq18 (X0 X1 X2 X4 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (((X4 ◇ (X4 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq24 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq15 eq18 -- forward demodulation 18,15
  have eq25 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq24 eq17 -- backward demodulation 17,24
  have eq29 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq25 eq9 -- backward demodulation 9,25
  have eq30 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X1) := superpose eq25 eq12 -- backward demodulation 12,25
  have eq32 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq25 eq24 -- backward demodulation 24,25
  have eq33 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq25 eq30 -- forward demodulation 30,25
  have eq42 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq32 eq32 -- superposition 32,32, 32 into 32, unify on (0).2 in 32 and (0).1.1 in 32
  have eq45 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X1 := superpose eq32 eq29 -- superposition 29,32, 32 into 29, unify on (0).2 in 32 and (0).1.1 in 29
  have eq46 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq42 eq10 -- backward demodulation 10,42
  have eq47 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq45 eq25 -- backward demodulation 25,45
  have eq52 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq47 eq46 -- backward demodulation 46,47
  have eq55 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ X1) = X0 := superpose eq47 eq33 -- backward demodulation 33,47
  have eq62 : sK0 ≠ (sK1 ◇ sK1) := superpose eq47 eq52 -- forward demodulation 52,47
  have eq64 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq47 eq55 -- forward demodulation 55,47
  have eq65 (X2 X3 : G) : X2 = X3 := superpose eq64 eq64 -- superposition 64,64, 64 into 64, unify on (0).2 in 64 and (0).1 in 64
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq62 -- superposition 62,64, 64 into 62, unify on (0).2 in 64 and (0).2 in 62
  subsumption eq67 eq65


@[equational_result]
theorem Equation1923_implies_Equation1369 (G : Type*) [Magma G] (h : Equation1923 G) : Equation1369 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK1) ◇ sK0) ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X3 X4 : G) : (((X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X4)) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq17 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X3 ◇ (X3 ◇ X0)) ◇ X0) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq18 (X0 X1 X2 X4 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (((X4 ◇ (X4 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq24 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq15 eq18 -- forward demodulation 18,15
  have eq25 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq24 eq17 -- backward demodulation 17,24
  have eq29 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq25 eq9 -- backward demodulation 9,25
  have eq30 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X1) := superpose eq25 eq12 -- backward demodulation 12,25
  have eq32 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq25 eq24 -- backward demodulation 24,25
  have eq33 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq25 eq30 -- forward demodulation 30,25
  have eq44 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X1 := superpose eq32 eq29 -- superposition 29,32, 32 into 29, unify on (0).2 in 32 and (0).1.1 in 29
  have eq45 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq44 eq25 -- backward demodulation 25,44
  have eq50 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ X1) = X0 := superpose eq45 eq33 -- backward demodulation 33,45
  have eq55 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK3)) := superpose eq45 eq10 -- backward demodulation 10,45
  have eq59 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq45 eq50 -- forward demodulation 50,45
  subsumption eq55 eq59


@[equational_result]
theorem Equation3196_implies_Equation490 (G : Type*) [Magma G] (h : Equation3196 G) : Equation490 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK3)))) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 (X2 X3 : G) : X2 = X3 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq18 (X0 : G) : sK0 ≠ (sK1 ◇ X0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq18 eq16


@[equational_result]
theorem Equation1896_implies_Equation776 (G : Type*) [Magma G] (h : Equation1896 G) : Equation776 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK2 ◇ sK0) ◇ sK2))) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq17 (X0 X2 : G) : ((X2 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq17 eq14 -- backward demodulation 14,17
  have eq24 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq47 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.2 in 12
  have eq49 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq47 eq19 -- backward demodulation 19,47
  have eq54 : sK0 ≠ (sK1 ◇ sK2) := superpose eq47 eq24 -- backward demodulation 24,47
  have eq56 (X0 X1 : G) : X0 = X1 := superpose eq49 eq47 -- superposition 47,49, 49 into 47, unify on (0).2 in 49 and (0).1 in 47
  have eq58 : sK0 ≠ sK1 := superpose eq47 eq54 -- superposition 54,47, 47 into 54, unify on (0).2 in 47 and (0).2 in 54
  subsumption eq58 eq56


@[equational_result]
theorem Equation2537_implies_Equation2092 (G : Type*) [Magma G] (h : Equation2537 G) : Equation2092 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq18 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X3)) ◇ (X0 ◇ X1)) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2.1 in 9
  have eq20 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ sK0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := superpose eq16 eq11 -- backward demodulation 11,16
  have eq26 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X2 := superpose eq12 eq18 -- forward demodulation 18,12
  have eq28 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1.2.2.1 in 25
  have eq44 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq16 eq28 -- forward demodulation 28,16
  have eq46 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X1 := superpose eq44 eq16 -- backward demodulation 16,44
  have eq49 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq46 eq26 -- backward demodulation 26,46
  have eq52 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq46 eq20 -- backward demodulation 20,46
  subsumption eq52 eq49


@[equational_result]
theorem Equation2921_implies_Equation890 (G : Type*) [Magma G] (h : Equation2921 G) : Equation890 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ (sK1 ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq19 (X0 X1 : G) : X0 = X1 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1 in 12
  have eq22 (X0 : G) : sK0 ≠ (X0 ◇ sK2) := superpose eq19 eq16 -- superposition 16,19, 19 into 16, unify on (0).2 in 19 and (0).2.1 in 16
  subsumption eq22 eq19


@[equational_result]
theorem Equation741_implies_Equation1358 (G : Type*) [Magma G] (h : Equation741 G) : Equation1358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK0) ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X2 ◇ X2) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq25 (X0 X1 : G) : sK0 ≠ (sK1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq25 eq17


@[equational_result]
theorem Equation741_implies_Equation1522 (G : Type*) [Magma G] (h : Equation741 G) : Equation1522 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X2 ◇ X2) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq23 (X0 X1 : G) : sK0 ≠ (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq23 eq17


@[equational_result]
theorem Equation3144_implies_Equation1490 (G : Type*) [Magma G] (h : Equation3144 G) : Equation1490 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq19 (X0 X1 : G) : sK0 ≠ ((X0 ◇ X0) ◇ X1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq19 eq17


@[equational_result]
theorem Equation2938_implies_Equation2922 (G : Type*) [Magma G] (h : Equation2938 G) : Equation2922 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) ◇ X2) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK3) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq18 (X1 X3 : G) : X1 = X3 := superpose eq13 eq16 -- superposition 16,13, 13 into 16, unify on (0).2 in 13 and (0).1 in 16
  have eq21 (X0 : G) : sK0 ≠ (X0 ◇ sK3) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2.1 in 15
  subsumption eq21 eq18


@[equational_result]
theorem Equation1280_implies_Equation2771 (G : Type*) [Magma G] (h : Equation1280 G) : Equation2771 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X1 X3 : G) : X1 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq20 (X0 : G) : sK0 ≠ (X0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation2901_implies_Equation1499 (G : Type*) [Magma G] (h : Equation2901 G) : Equation1499 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation3194_implies_Equation884 (G : Type*) [Magma G] (h : Equation3194 G) : Equation884 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq17 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK1 ◇ sK0) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq20 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq12 eq14 -- superposition 14,12, 12 into 14, unify on (0).2 in 12 and (0).2 in 14
  have eq30 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq20 eq9 -- backward demodulation 9,20
  have eq42 (X2 X3 : G) : X2 = X3 := superpose eq30 eq30 -- superposition 30,30, 30 into 30, unify on (0).2 in 30 and (0).1 in 30
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq18 -- superposition 18,42, 42 into 18, unify on (0).2 in 42 and (0).2 in 18
  subsumption eq56 eq42


@[equational_result]
theorem Equation488_implies_Equation2788 (G : Type*) [Magma G] (h : Equation488 G) : Equation2788 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq14 (X0 X1 : G) : X0 = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq19 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 : sK0 ≠ (sK1 ◇ sK1) := superpose eq12 eq19 -- forward demodulation 19,12
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq20 -- superposition 20,14, 14 into 20, unify on (0).2 in 14 and (0).2 in 20
  subsumption eq27 eq14


@[equational_result]
theorem Equation1156_implies_Equation2110 (G : Type*) [Magma G] (h : Equation1156 G) : Equation2110 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK2) ◇ (sK0 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X2) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X2 X3 : G) : X2 = X3 := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1 in 14
  have eq21 (X0 : G) : sK0 ≠ (X0 ◇ (sK0 ◇ sK3)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.1 in 10
  subsumption eq21 eq15


@[equational_result]
theorem Equation2382_implies_Equation1156 (G : Type*) [Magma G] (h : Equation2382 G) : Equation1156 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X2 X3 : G) : X2 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq19 (X0 : G) : sK0 ≠ (sK1 ◇ X0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq19 eq16


@[equational_result]
theorem Equation496_implies_Equation2713 (G : Type*) [Magma G] (h : Equation496 G) : Equation2713 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ X1) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq17 (X1 X2 : G) : X1 = X2 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq14 -- superposition 14,17, 17 into 14, unify on (0).2 in 17 and (0).2 in 14
  subsumption eq27 eq17


@[equational_result]
theorem Equation1905_implies_Equation471 (G : Type*) [Magma G] (h : Equation1905 G) : Equation471 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq23 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) := superpose eq18 eq10 -- backward demodulation 10,18
  have eq26 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.2 in 9
  have eq29 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.1 in 9
  have eq86 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq18 eq13 -- superposition 13,18, 18 into 13, unify on (0).2 in 18 and (0).1 in 13
  have eq94 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq11 eq13 -- superposition 13,11, 11 into 13, unify on (0).2 in 11 and (0).2.1 in 13
  have eq107 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq26 eq94 -- forward demodulation 94,26
  have eq108 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq107 eq86 -- backward demodulation 86,107
  have eq110 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq107 eq29 -- backward demodulation 29,107
  have eq113 : sK0 ≠ (sK1 ◇ sK0) := superpose eq107 eq23 -- backward demodulation 23,107
  have eq117 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq110 eq108 -- backward demodulation 108,110
  have eq121 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq117 eq9 -- backward demodulation 9,117
  have eq156 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq117 eq121 -- forward demodulation 121,117
  have eq157 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq117 eq156 -- forward demodulation 156,117
  subsumption eq113 eq157


@[equational_result]
theorem Equation681_implies_Equation705 (G : Type*) [Magma G] (h : Equation681 G) : Equation705 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq14 eq11


@[equational_result]
theorem Equation3177_implies_Equation1765 (G : Type*) [Magma G] (h : Equation3177 G) : Equation1765 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1.1 in 9
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq19 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ sK0)) := superpose eq18 eq10 -- backward demodulation 10,18
  have eq24 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2))) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq38 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).1.2 in 13
  have eq41 (X0 X2 X3 : G) : (X2 ◇ ((X0 ◇ X3) ◇ X0)) = X0 := superpose eq18 eq24 -- forward demodulation 24,18
  have eq42 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq38 eq16 -- backward demodulation 16,38
  have eq48 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq42 eq41 -- backward demodulation 41,42
  have eq51 : sK0 ≠ ((sK1 ◇ sK2) ◇ sK2) := superpose eq42 eq19 -- backward demodulation 19,42
  subsumption eq51 eq48


@[equational_result]
theorem Equation470_implies_Equation3177 (G : Type*) [Magma G] (h : Equation470 G) : Equation3177 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK2) ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq17 (X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X1))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2.2 in 9
  have eq18 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X2)) := superpose eq13 eq18 -- forward demodulation 18,13
  have eq32 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ X0)) ◇ X1) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq39 (X0 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X2 ◇ X0)) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).1.1 in 13
  have eq41 (X0 X1 X3 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ X1) = X0 := superpose eq19 eq32 -- forward demodulation 32,19
  have eq42 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq39 eq17 -- backward demodulation 17,39
  have eq47 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq42 eq41 -- backward demodulation 41,42
  have eq51 (X0 X1 : G) : X0 = X1 := superpose eq16 eq47 -- superposition 47,16, 16 into 47, unify on (0).2 in 16 and (0).1 in 47
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq14 -- superposition 14,47, 47 into 14, unify on (0).2 in 47 and (0).2 in 14
  subsumption eq61 eq51


@[equational_result]
theorem Equation2365_implies_Equation1077 (G : Type*) [Magma G] (h : Equation2365 G) : Equation1077 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X2 X3 : G) : X2 = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq25 (X0 X1 : G) : sK0 ≠ (sK1 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2.2 in 10
  subsumption eq25 eq16


@[equational_result]
theorem Equation747_implies_Equation705 (G : Type*) [Magma G] (h : Equation747 G) : Equation705 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK2))) := mod_symm nh
  have eq13 (X1 X2 X3 : G) : (X2 ◇ X3) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X2 X4 : G) : X2 = X4 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq20 (X0 : G) : sK0 ≠ (sK1 ◇ (sK1 ◇ X0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.2 in 10
  subsumption eq20 eq14


@[equational_result]
theorem Equation555_implies_Equation874 (G : Type*) [Magma G] (h : Equation555 G) : Equation874 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq22 (X1 X2 : G) : X1 = X2 := superpose eq12 eq16 -- superposition 16,12, 12 into 16, unify on (0).2 in 12 and (0).1 in 16
  have eq29 (X0 : G) : sK0 ≠ (sK1 ◇ X0) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2 in 10
  subsumption eq29 eq22


@[equational_result]
theorem Equation3025_implies_Equation708 (G : Type*) [Magma G] (h : Equation3025 G) : Equation708 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK2))) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : (((X4 ◇ X3) ◇ X5) ◇ X4) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq17 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq26 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq17 eq10 -- backward demodulation 10,17
  subsumption eq26 eq17


@[equational_result]
theorem Equation689_implies_Equation1350 (G : Type*) [Magma G] (h : Equation689 G) : Equation1350 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK0) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 X5 : G) : (X5 ◇ (X1 ◇ X2)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq20 (X1 X2 : G) : X1 = X2 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1 in 12
  have eq21 : sK0 ≠ ((sK2 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq21 eq20


@[equational_result]
theorem Equation2099_implies_Equation673 (G : Type*) [Magma G] (h : Equation2099 G) : Equation673 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq16 (X0 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq18 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq16 eq14 -- backward demodulation 14,16
  have eq21 (X1 X2 X3 : G) : (X1 ◇ X2) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq18 eq11 -- backward demodulation 11,18
  have eq24 (X1 X2 X3 : G) : (X1 ◇ X2) = (X1 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq15 eq21 -- forward demodulation 21,15
  have eq25 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK2)) := superpose eq24 eq10 -- backward demodulation 10,24
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq24 -- superposition 24,12, 12 into 24, unify on (0).2 in 12 and (0).2.2 in 24
  have eq35 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq31 -- forward demodulation 31,12
  have eq37 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq35 eq18 -- backward demodulation 18,35
  have eq39 : sK0 ≠ (sK1 ◇ sK0) := superpose eq35 eq25 -- backward demodulation 25,35
  have eq43 (X1 X2 : G) : X1 = X2 := superpose eq37 eq37 -- superposition 37,37, 37 into 37, unify on (0).2 in 37 and (0).1 in 37
  have eq51 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq37 eq39 -- superposition 39,37, 37 into 39, unify on (0).2 in 37 and (0).2 in 39
  subsumption eq51 eq43


@[equational_result]
theorem Equation1501_implies_Equation2975 (G : Type*) [Magma G] (h : Equation1501 G) : Equation2975 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq13 (X1 X2 X4 : G) : ((X4 ◇ X2) ◇ X1) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ ((sK2 ◇ sK0) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation573_implies_Equation1296 (G : Type*) [Magma G] (h : Equation573 G) : Equation1296 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK2) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.1 in 12
  have eq21 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2))) = X0 := superpose eq15 eq11 -- backward demodulation 11,15
  have eq37 (X3 X4 : G) : X3 = X4 := superpose eq21 eq21 -- superposition 21,21, 21 into 21, unify on (0).2 in 21 and (0).1 in 21
  have eq65 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq37 eq10 -- superposition 10,37, 37 into 10, unify on (0).2 in 37 and (0).2.2.1 in 10
  subsumption eq65 eq37


@[equational_result]
theorem Equation2771_implies_Equation2977 (G : Type*) [Magma G] (h : Equation2771 G) : Equation2977 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK0)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq21 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq21 -- superposition 21,16, 16 into 21, unify on (0).2 in 16 and (0).2 in 21
  subsumption eq29 eq16


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
theorem Equation1698_implies_Equation63 (G : Type*) [Magma G] (h : Equation1698 G) : Equation63 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ (X0 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ (((X0 ◇ X2) ◇ X0) ◇ X1)) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1 in 12
  have eq33 (X1 X3 X4 : G) : ((X1 ◇ X3) ◇ X1) = ((X1 ◇ X4) ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2 in 11
  have eq35 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X2) ◇ X3) ◇ (X0 ◇ X2))) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1 in 12
  have eq44 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq9 eq33 -- superposition 33,9, 9 into 33, unify on (0).2 in 9 and (0).1.1 in 33
  have eq91 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq44 eq35 -- backward demodulation 35,44
  have eq146 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (((X2 ◇ X3) ◇ X2) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).1.1 in 12
  have eq163 (X0 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3)) = X4 := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).1.2.1 in 15
  have eq166 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = X2 := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2 in 15
  have eq232 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1) = X0 := superpose eq13 eq166 -- superposition 166,13, 13 into 166, unify on (0).2 in 13 and (0).1.1 in 166
  have eq252 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ X0) = X4 := superpose eq232 eq163 -- backward demodulation 163,232
  have eq259 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq252 eq146 -- backward demodulation 146,252
  have eq319 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq252 eq259 -- forward demodulation 259,252
  have eq321 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq319 eq91 -- backward demodulation 91,319
  have eq322 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq319 eq232 -- backward demodulation 232,319
  have eq323 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X0 := superpose eq321 eq13 -- backward demodulation 13,321
  have eq328 (X0 X2 : G) : X0 = X2 := superpose eq323 eq322 -- superposition 322,323, 323 into 322, unify on (0).2 in 323 and (0).1 in 322
  have eq333 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ X0)) := superpose eq322 eq10 -- superposition 10,322, 322 into 10, unify on (0).2 in 322 and (0).2.2.2 in 10
  subsumption eq333 eq328


@[equational_result]
theorem Equation1698_implies_Equation555 (G : Type*) [Magma G] (h : Equation1698 G) : Equation555 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ (X0 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ (((X0 ◇ X2) ◇ X0) ◇ X1)) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1 in 12
  have eq146 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (((X2 ◇ X3) ◇ X2) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).1.1 in 12
  have eq163 (X0 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3)) = X4 := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).1.2.1 in 15
  have eq166 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = X2 := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2 in 15
  have eq232 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1) = X0 := superpose eq13 eq166 -- superposition 166,13, 13 into 166, unify on (0).2 in 13 and (0).1.1 in 166
  have eq252 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ X0) = X4 := superpose eq232 eq163 -- backward demodulation 163,232
  have eq259 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq252 eq146 -- backward demodulation 146,252
  have eq319 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq252 eq259 -- forward demodulation 259,252
  have eq322 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq319 eq232 -- backward demodulation 232,319
  have eq323 : sK0 ≠ (sK1 ◇ sK1) := superpose eq319 eq10 -- backward demodulation 10,319
  subsumption eq323 eq322


@[equational_result]
theorem Equation1324_implies_Equation886 (G : Type*) [Magma G] (h : Equation1324 G) : Equation886 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X1 X3 : G) : X1 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq19 (X0 : G) : sK0 ≠ (sK1 ◇ X0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq19 eq13


@[equational_result]
theorem Equation674_implies_Equation1076 (G : Type*) [Magma G] (h : Equation674 G) : Equation1076 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation674_implies_Equation668 (G : Type*) [Magma G] (h : Equation674 G) : Equation668 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation2914_implies_Equation1501 (G : Type*) [Magma G] (h : Equation2914 G) : Equation1501 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK3))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq24 (X3 X4 : G) : X3 = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq10 -- superposition 10,24, 24 into 10, unify on (0).2 in 24 and (0).2 in 10
  subsumption eq78 eq24


@[equational_result]
theorem Equation493_implies_Equation2991 (G : Type*) [Magma G] (h : Equation493 G) : Equation2991 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK1)) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq17 (X0 X3 X4 : G) : (X3 ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq26 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq17 eq9 -- backward demodulation 9,17
  have eq27 : sK0 ≠ ((sK2 ◇ sK0) ◇ sK1) := superpose eq17 eq10 -- backward demodulation 10,17
  subsumption eq27 eq26


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
theorem Equation1102_implies_Equation1925 (G : Type*) [Magma G] (h : Equation1102 G) : Equation1925 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 (X1 X3 : G) : X1 = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq17 (X0 : G) : sK0 ≠ ((sK1 ◇ X0) ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.2 in 10
  subsumption eq17 eq14


@[equational_result]
theorem Equation1102_implies_Equation484 (G : Type*) [Magma G] (h : Equation1102 G) : Equation484 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 (X1 X3 : G) : X1 = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq21 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ X0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.2.2 in 10
  subsumption eq21 eq14


@[equational_result]
theorem Equation1317_implies_Equation1152 (G : Type*) [Magma G] (h : Equation1317 G) : Equation1152 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X1 X3 : G) : X1 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq18 (X0 : G) : sK0 ≠ (sK1 ◇ X0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq18 eq13


@[equational_result]
theorem Equation1317_implies_Equation678 (G : Type*) [Magma G] (h : Equation1317 G) : Equation678 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X1 X3 : G) : X1 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq18 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2.2 in 10
  subsumption eq18 eq13


@[equational_result]
theorem Equation2945_implies_Equation1317 (G : Type*) [Magma G] (h : Equation2945 G) : Equation1317 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq13 (X1 X2 X4 : G) : (X1 ◇ X4) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X1 X4 : G) : X1 = X4 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq18 (X0 : G) : sK0 ≠ (sK1 ◇ ((X0 ◇ sK1) ◇ sK2)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.1.1 in 10
  subsumption eq18 eq15


@[equational_result]
theorem Equation2945_implies_Equation1148 (G : Type*) [Magma G] (h : Equation2945 G) : Equation1148 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK0 ◇ sK0)) ◇ sK2)) := mod_symm nh
  have eq13 (X1 X2 X4 : G) : (X1 ◇ X4) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X1 X4 : G) : X1 = X4 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq20 (X0 : G) : sK0 ≠ (sK1 ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  subsumption eq20 eq15


@[equational_result]
theorem Equation2945_implies_Equation681 (G : Type*) [Magma G] (h : Equation2945 G) : Equation681 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK2))) := mod_symm nh
  have eq13 (X1 X2 X4 : G) : (X1 ◇ X4) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X1 X4 : G) : X1 = X4 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq20 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ X0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.2 in 10
  subsumption eq20 eq15


@[equational_result]
theorem Equation2721_implies_Equation431 (G : Type*) [Magma G] (h : Equation2721 G) : Equation431 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq43 (X2 X3 : G) : X2 = X3 := superpose eq16 eq16 -- superposition 16,16, 16 into 16, unify on (0).2 in 16 and (0).1 in 16
  have eq56 (X0 X1 : G) : sK0 ≠ (sK0 ◇ (sK1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2.2 in 10
  subsumption eq56 eq43


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
theorem Equation547_implies_Equation2128 (G : Type*) [Magma G] (h : Equation547 G) : Equation2128 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq19 eq17


@[equational_result]
theorem Equation547_implies_Equation691 (G : Type*) [Magma G] (h : Equation547 G) : Equation691 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK2 ◇ sK1) ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq19 (X0 X1 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2.2 in 10
  subsumption eq19 eq17


@[equational_result]
theorem Equation589_implies_Equation547 (G : Type*) [Magma G] (h : Equation589 G) : Equation547 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1 in 13
  have eq26 (X0 X1 : G) : sK0 ≠ ((X0 ◇ X1) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq26 eq17


@[equational_result]
theorem Equation673_implies_Equation2297 (G : Type*) [Magma G] (h : Equation673 G) : Equation2297 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq16 eq13 -- backward demodulation 13,16
  have eq23 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq21 eq11 -- backward demodulation 11,21
  have eq27 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq21 eq10 -- backward demodulation 10,21
  subsumption eq27 eq23


@[equational_result]
theorem Equation673_implies_Equation1294 (G : Type*) [Magma G] (h : Equation673 G) : Equation1294 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK1) ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq16 eq13 -- backward demodulation 13,16
  have eq23 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq21 eq11 -- backward demodulation 11,21
  have eq27 (X2 X3 : G) : X2 = X3 := superpose eq23 eq23 -- superposition 23,23, 23 into 23, unify on (0).2 in 23 and (0).1 in 23
  have eq29 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ sK3)) := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2.2.1 in 10
  subsumption eq29 eq27


@[equational_result]
theorem Equation2907_implies_Equation1522 (G : Type*) [Magma G] (h : Equation2907 G) : Equation1522 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1 in 11
  have eq18 (X0 X1 : G) : sK0 ≠ ((X0 ◇ X1) ◇ X1) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 eq16


@[equational_result]
theorem Equation2907_implies_Equation68 (G : Type*) [Magma G] (h : Equation2907 G) : Equation68 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1 in 11
  have eq18 (X0 X1 : G) : sK0 ≠ ((X0 ◇ X1) ◇ X1) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 eq16


@[equational_result]
theorem Equation468_implies_Equation2907 (G : Type*) [Magma G] (h : Equation468 G) : Equation2907 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X3 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK2) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq18 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X1)) = X3 := superpose eq17 eq11 -- backward demodulation 11,17
  have eq20 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq18 eq17 -- backward demodulation 17,18
  have eq21 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq20 eq18 -- backward demodulation 18,20
  have eq23 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK2) := superpose eq20 eq14 -- backward demodulation 14,20
  have eq24 : sK0 ≠ (sK1 ◇ sK2) := superpose eq20 eq23 -- forward demodulation 23,20
  have eq27 (X0 X1 : G) : X0 = X1 := superpose eq21 eq20 -- superposition 20,21, 21 into 20, unify on (0).2 in 21 and (0).1 in 20
  have eq29 : sK0 ≠ sK1 := superpose eq20 eq24 -- superposition 24,20, 20 into 24, unify on (0).2 in 20 and (0).2 in 24
  subsumption eq29 eq27


@[equational_result]
theorem Equation1287_implies_Equation468 (G : Type*) [Magma G] (h : Equation1287 G) : Equation468 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X1 X3 : G) : X1 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq20 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2.2 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation507_implies_Equation890 (G : Type*) [Magma G] (h : Equation507 G) : Equation890 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq28 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq29 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq35 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq29 eq28 -- backward demodulation 28,29
  have eq51 : sK0 ≠ (sK1 ◇ sK0) := superpose eq29 eq10 -- backward demodulation 10,29
  have eq52 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq29 eq35 -- forward demodulation 35,29
  subsumption eq51 eq52


@[equational_result]
theorem Equation1554_implies_Equation2251 (G : Type*) [Magma G] (h : Equation1554 G) : Equation2251 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq20 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq24 (X1 X2 : G) : (X1 ◇ X2) = (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X2)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.1 in 13
  have eq39 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq20 eq9 -- superposition 9,20, 20 into 9, unify on (0).2 in 20 and (0).1.2.2 in 9
  have eq42 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq20 eq39 -- forward demodulation 39,20
  have eq44 (X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ (X1 ◇ X2)) := superpose eq42 eq24 -- backward demodulation 24,42
  have eq45 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq19 eq44 -- forward demodulation 44,19
  have eq60 : sK0 ≠ (sK0 ◇ sK2) := superpose eq45 eq10 -- backward demodulation 10,45
  subsumption eq60 eq45


@[equational_result]
theorem Equation1554_implies_Equation1367 (G : Type*) [Magma G] (h : Equation1554 G) : Equation1367 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK1) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq20 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq24 (X1 X2 : G) : (X1 ◇ X2) = (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X2)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.1 in 13
  have eq39 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq20 eq9 -- superposition 9,20, 20 into 9, unify on (0).2 in 20 and (0).1.2.2 in 9
  have eq42 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq20 eq39 -- forward demodulation 39,20
  have eq44 (X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ (X1 ◇ X2)) := superpose eq42 eq24 -- backward demodulation 24,42
  have eq45 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq19 eq44 -- forward demodulation 44,19
  have eq46 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq45 eq9 -- backward demodulation 9,45
  have eq60 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK1)) := superpose eq45 eq10 -- backward demodulation 10,45
  have eq61 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq45 eq46 -- forward demodulation 46,45
  have eq72 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK1)) := superpose eq45 eq60 -- forward demodulation 60,45
  have eq73 : sK0 ≠ (sK1 ◇ sK2) := superpose eq45 eq72 -- forward demodulation 72,45
  have eq77 (X0 X1 : G) : X0 = X1 := superpose eq61 eq45 -- superposition 45,61, 61 into 45, unify on (0).2 in 61 and (0).1 in 45
  have eq79 : sK0 ≠ sK1 := superpose eq45 eq73 -- superposition 73,45, 45 into 73, unify on (0).2 in 45 and (0).2 in 73
  subsumption eq79 eq77


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
theorem Equation2918_implies_Equation2537 (G : Type*) [Magma G] (h : Equation2918 G) : Equation2537 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq13 (X1 X2 X4 : G) : (X1 ◇ X4) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X1 X4 : G) : X1 = X4 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq17 (X0 : G) : sK0 ≠ ((sK1 ◇ (X0 ◇ sK2)) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.2.1 in 10
  subsumption eq17 eq14


@[equational_result]
theorem Equation2918_implies_Equation1287 (G : Type*) [Magma G] (h : Equation2918 G) : Equation1287 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq13 (X1 X2 X4 : G) : (X1 ◇ X4) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X1 X4 : G) : X1 = X4 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq21 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ sK2)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.1 in 10
  subsumption eq21 eq14


@[equational_result]
theorem Equation758_implies_Equation671 (G : Type*) [Magma G] (h : Equation758 G) : Equation671 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq25 (X0 X1 : G) : sK0 ≠ (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq25 eq17


@[equational_result]
theorem Equation1886_implies_Equation2108 (G : Type*) [Magma G] (h : Equation1886 G) : Equation2108 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK2) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq15 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq16 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq18 (X0 X2 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq16 eq15 -- backward demodulation 15,16
  have eq23 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X0 := superpose eq16 eq18 -- forward demodulation 18,16
  have eq24 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq23 eq19 -- backward demodulation 19,23
  have eq27 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq24 eq14 -- backward demodulation 14,24
  have eq29 : sK0 ≠ (sK2 ◇ (sK0 ◇ sK1)) := superpose eq24 eq10 -- backward demodulation 10,24
  have eq30 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq24 eq27 -- forward demodulation 27,24
  have eq31 : sK0 ≠ (sK2 ◇ sK1) := superpose eq24 eq29 -- forward demodulation 29,24
  have eq33 (X0 X1 : G) : X0 = X1 := superpose eq30 eq24 -- superposition 24,30, 30 into 24, unify on (0).2 in 30 and (0).1 in 24
  have eq34 : sK0 ≠ sK1 := superpose eq24 eq31 -- superposition 31,24, 24 into 31, unify on (0).2 in 24 and (0).2 in 31
  subsumption eq34 eq33


@[equational_result]
theorem Equation3117_implies_Equation1886 (G : Type*) [Magma G] (h : Equation3117 G) : Equation1886 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2 in 12
  have eq21 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ X1) ◇ X3) = X2 := superpose eq15 eq11 -- backward demodulation 11,15
  have eq37 (X3 X4 : G) : X3 = X4 := superpose eq21 eq21 -- superposition 21,21, 21 into 21, unify on (0).2 in 21 and (0).1 in 21
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq10 -- superposition 10,37, 37 into 10, unify on (0).2 in 37 and (0).2 in 10
  subsumption eq58 eq37


@[equational_result]
theorem Equation3117_implies_Equation2957 (G : Type*) [Magma G] (h : Equation3117 G) : Equation2957 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK2)) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2 in 12
  have eq21 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ X1) ◇ X3) = X2 := superpose eq15 eq11 -- backward demodulation 11,15
  have eq37 (X3 X4 : G) : X3 = X4 := superpose eq21 eq21 -- superposition 21,21, 21 into 21, unify on (0).2 in 21 and (0).1 in 21
  have eq53 (X0 : G) : sK0 ≠ (((sK1 ◇ X0) ◇ sK0) ◇ sK1) := superpose eq37 eq10 -- superposition 10,37, 37 into 10, unify on (0).2 in 37 and (0).2.1.1.2 in 10
  subsumption eq53 eq37


@[equational_result]
theorem Equation1702_implies_Equation1276 (G : Type*) [Magma G] (h : Equation1702 G) : Equation1276 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X0) = (X1 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X0) = ((X3 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((((X2 ◇ X1) ◇ X0) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq18 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq22 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq16 eq10 -- backward demodulation 10,16
  have eq27 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.1 in 9
  have eq29 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.2 in 9
  have eq48 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X0) = (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ (X2 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq80 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq18 eq11 -- superposition 11,18, 18 into 11, unify on (0).2 in 18 and (0).1 in 11
  have eq94 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq107 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq27 eq94 -- forward demodulation 94,27
  have eq109 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq107 eq80 -- backward demodulation 80,107
  have eq110 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq107 eq29 -- backward demodulation 29,107
  have eq114 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq110 eq109 -- backward demodulation 109,110
  have eq138 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) = X0 := superpose eq114 eq48 -- backward demodulation 48,114
  have eq153 : sK0 ≠ (sK1 ◇ sK1) := superpose eq114 eq22 -- backward demodulation 22,114
  have eq180 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = X0 := superpose eq114 eq138 -- forward demodulation 138,114
  have eq181 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := superpose eq114 eq180 -- forward demodulation 180,114
  have eq182 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq114 eq181 -- forward demodulation 181,114
  subsumption eq153 eq182


@[equational_result]
theorem Equation1702_implies_Equation740 (G : Type*) [Magma G] (h : Equation1702 G) : Equation740 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK0 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X0) = (X1 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X0) = ((X3 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((((X2 ◇ X1) ◇ X0) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq18 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq22 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq16 eq10 -- backward demodulation 10,16
  have eq27 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.1 in 9
  have eq29 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.2 in 9
  have eq80 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq18 eq11 -- superposition 11,18, 18 into 11, unify on (0).2 in 18 and (0).1 in 11
  have eq94 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq107 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq27 eq94 -- forward demodulation 94,27
  have eq109 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq107 eq80 -- backward demodulation 80,107
  have eq110 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq107 eq29 -- backward demodulation 29,107
  have eq114 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq110 eq109 -- backward demodulation 109,110
  have eq153 : sK0 ≠ (sK1 ◇ sK0) := superpose eq114 eq22 -- backward demodulation 22,114
  subsumption eq153 eq114


@[equational_result]
theorem Equation1702_implies_Equation2982 (G : Type*) [Magma G] (h : Equation1702 G) : Equation2982 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK0)) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X0) = (X1 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X0) = ((X3 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((((X2 ◇ X1) ◇ X0) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq40 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X0) = (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ (X2 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq46 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.1 in 9
  have eq50 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.2 in 9
  have eq59 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq18 eq11 -- superposition 11,18, 18 into 11, unify on (0).2 in 18 and (0).1 in 11
  have eq71 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq82 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq46 eq71 -- forward demodulation 71,46
  have eq84 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq82 eq59 -- backward demodulation 59,82
  have eq85 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq82 eq50 -- backward demodulation 50,82
  have eq89 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq85 eq84 -- backward demodulation 84,85
  have eq109 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) = X0 := superpose eq89 eq40 -- backward demodulation 40,89
  have eq124 : sK0 ≠ (sK2 ◇ sK1) := superpose eq89 eq10 -- backward demodulation 10,89
  have eq148 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = X0 := superpose eq89 eq109 -- forward demodulation 109,89
  have eq149 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := superpose eq89 eq148 -- forward demodulation 148,89
  have eq150 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq89 eq149 -- forward demodulation 149,89
  have eq191 (X1 X2 : G) : X1 = X2 := superpose eq150 eq150 -- superposition 150,150, 150 into 150, unify on (0).2 in 150 and (0).1 in 150
  have eq199 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq150 eq124 -- superposition 124,150, 150 into 124, unify on (0).2 in 150 and (0).2 in 124
  subsumption eq199 eq191


@[equational_result]
theorem Equation1702_implies_Equation747 (G : Type*) [Magma G] (h : Equation1702 G) : Equation747 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK0 ◇ sK1) ◇ sK3))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X0) = (X1 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X0) = ((X3 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((((X2 ◇ X1) ◇ X0) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq40 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X0) = (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ (X2 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq46 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.1 in 9
  have eq50 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.2 in 9
  have eq59 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq18 eq11 -- superposition 11,18, 18 into 11, unify on (0).2 in 18 and (0).1 in 11
  have eq71 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq82 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq46 eq71 -- forward demodulation 71,46
  have eq84 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq82 eq59 -- backward demodulation 59,82
  have eq85 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq82 eq50 -- backward demodulation 50,82
  have eq89 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq85 eq84 -- backward demodulation 84,85
  have eq109 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) = X0 := superpose eq89 eq40 -- backward demodulation 40,89
  have eq124 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK3)) := superpose eq89 eq10 -- backward demodulation 10,89
  have eq148 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = X0 := superpose eq89 eq109 -- forward demodulation 109,89
  have eq149 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := superpose eq89 eq148 -- forward demodulation 148,89
  have eq150 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq89 eq149 -- forward demodulation 149,89
  have eq172 : sK0 ≠ (sK1 ◇ sK3) := superpose eq89 eq124 -- forward demodulation 124,89
  have eq192 (X1 X2 : G) : X1 = X2 := superpose eq150 eq150 -- superposition 150,150, 150 into 150, unify on (0).2 in 150 and (0).1 in 150
  have eq200 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq150 eq172 -- superposition 172,150, 150 into 172, unify on (0).2 in 150 and (0).2 in 172
  subsumption eq200 eq192


@[equational_result]
theorem Equation1369_implies_Equation1702 (G : Type*) [Magma G] (h : Equation1369 G) : Equation1702 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq13 (X1 X2 X4 : G) : (X1 ◇ X4) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X2 X4 : G) : X2 = X4 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq20 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 eq14


@[equational_result]
theorem Equation482_implies_Equation465 (G : Type*) [Magma G] (h : Equation482 G) : Equation465 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq11 (X1 X4 X5 : G) : (X4 ◇ (X5 ◇ (X4 ◇ X1))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X4 : G) : (X0 ◇ (X4 ◇ X1)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : sK0 ≠ (sK1 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq17 (X1 X2 : G) : X1 = X2 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq19 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  subsumption eq19 eq17


@[equational_result]
theorem Equation482_implies_Equation488 (G : Type*) [Magma G] (h : Equation482 G) : Equation488 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X0 ◇ (X4 ◇ X1)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ (sK1 ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 (X1 X2 : G) : X1 = X2 := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq19 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).2 in 16
  subsumption eq19 eq17


@[equational_result]
theorem Equation750_implies_Equation3983 (G : Type*) [Magma G] (h : Equation750 G) : Equation3983 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X2 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X2)) = X0 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq21 (X2 X3 X4 : G) : (X3 ◇ X2) = X4 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq24 (X3 X4 : G) : X3 = X4 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1 in 13
  have eq39 (X0 : G) : (sK0 ◇ sK1) ≠ X0 := superpose eq24 eq10 -- superposition 10,24, 24 into 10, unify on (0).2 in 24 and (0).2 in 10
  subsumption eq39 eq21


@[equational_result]
theorem Equation750_implies_Equation751 (G : Type*) [Magma G] (h : Equation750 G) : Equation751 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ sK3))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X2 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X2)) = X0 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq24 (X3 X4 : G) : X3 = X4 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1 in 13
  have eq39 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ X0)) := superpose eq24 eq10 -- superposition 10,24, 24 into 10, unify on (0).2 in 24 and (0).2.2.2 in 10
  subsumption eq39 eq24


@[equational_result]
theorem Equation1976_implies_Equation2983 (G : Type*) [Magma G] (h : Equation1976 G) : Equation2983 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK0)) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X2) ◇ (X3 ◇ (X2 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (((X2 ◇ X0) ◇ (X3 ◇ (X2 ◇ X0))) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X3 ◇ X2)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (((X2 ◇ X0) ◇ X2) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq33 (X1 X3 X4 : G) : (X1 ◇ (X3 ◇ X1)) = (X1 ◇ (X4 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2 in 12
  have eq44 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X2 ◇ X0) ◇ (X3 ◇ (X2 ◇ X0))) := superpose eq9 eq33 -- superposition 33,9, 9 into 33, unify on (0).2 in 9 and (0).1.2 in 33
  have eq49 (X0 X1 X3 X4 : G) : (X0 ◇ (X1 ◇ (X3 ◇ X1))) = (X0 ◇ (X4 ◇ X0)) := superpose eq12 eq33 -- superposition 33,12, 12 into 33, unify on (0).2 in 12 and (0).1.2 in 33
  have eq65 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := superpose eq33 eq11 -- superposition 11,33, 33 into 11, unify on (0).2 in 33 and (0).1.2 in 11
  have eq123 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq139 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) = X3 := superpose eq44 eq123 -- forward demodulation 123,44
  have eq150 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X0))) = X0 := superpose eq33 eq139 -- superposition 139,33, 33 into 139, unify on (0).2 in 33 and (0).1.2 in 139
  have eq162 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X2)) = X3 := superpose eq150 eq13 -- backward demodulation 13,150
  have eq176 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X0)) = (X0 ◇ X3) := superpose eq162 eq49 -- backward demodulation 49,162
  have eq177 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq162 eq65 -- backward demodulation 65,162
  have eq199 : sK0 ≠ ((sK2 ◇ sK2) ◇ sK2) := superpose eq162 eq10 -- backward demodulation 10,162
  have eq200 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq177 eq15 -- backward demodulation 15,177
  have eq205 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq200 eq176 -- backward demodulation 176,200
  have eq207 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X0 := superpose eq205 eq177 -- backward demodulation 177,205
  have eq209 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq205 eq207 -- forward demodulation 207,205
  subsumption eq199 eq209


@[equational_result]
theorem Equation484_implies_Equation3967 (G : Type*) [Magma G] (h : Equation484 G) : Equation3967 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X3 ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq18 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X3 ◇ X1))) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq19 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq14 eq9 -- backward demodulation 9,14
  have eq20 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq17 eq18 -- backward demodulation 18,17
  have eq21 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ X1) := superpose eq17 eq14 -- backward demodulation 14,17
  have eq24 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq25 : (sK1 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq21 eq24 -- forward demodulation 24,21
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq13 eq20 -- superposition 20,13, 13 into 20, unify on (0).2 in 13 and (0).1.1 in 20
  have eq30 (X1 X2 : G) : X1 = X2 := superpose eq19 eq20 -- superposition 20,19, 19 into 20, unify on (0).2 in 19 and (0).1 in 20
  have eq40 (X0 : G) : (sK0 ◇ sK0) ≠ X0 := superpose eq30 eq25 -- superposition 25,30, 30 into 25, unify on (0).2 in 30 and (0).1 in 25
  subsumption eq40 eq27


@[equational_result]
theorem Equation484_implies_Equation470 (G : Type*) [Magma G] (h : Equation484 G) : Equation470 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X3 ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq18 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X3 ◇ X1))) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq19 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq14 eq9 -- backward demodulation 9,14
  have eq20 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq17 eq18 -- backward demodulation 18,17
  have eq24 : sK0 ≠ (sK1 ◇ sK0) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq29 (X1 X2 : G) : X1 = X2 := superpose eq19 eq20 -- superposition 20,19, 19 into 20, unify on (0).2 in 19 and (0).1 in 20
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq24 -- superposition 24,29, 29 into 24, unify on (0).2 in 29 and (0).2 in 24
  subsumption eq39 eq29


@[equational_result]
theorem Equation478_implies_Equation480 (G : Type*) [Magma G] (h : Equation478 G) : Equation480 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq22 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq26 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.2 in 11
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq22 eq26 -- forward demodulation 26,22
  have eq30 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq29 eq22 -- backward demodulation 22,29
  have eq34 : sK0 ≠ (sK1 ◇ sK0) := superpose eq29 eq14 -- backward demodulation 14,29
  subsumption eq34 eq30


@[equational_result]
theorem Equation794_implies_Equation1688 (G : Type*) [Magma G] (h : Equation794 G) : Equation1688 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq13 (X2 X3 X4 : G) : (X4 ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X3 X4 : G) : X3 = X4 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq20 (X0 : G) : sK0 ≠ ((sK1 ◇ sK0) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  subsumption eq20 eq14


@[equational_result]
theorem Equation1703_implies_Equation2113 (G : Type*) [Magma G] (h : Equation1703 G) : Equation2113 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK2) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq13 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X2 : G) : ((X2 ◇ X1) ◇ X2) = (X1 ◇ ((X2 ◇ X1) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq18 (X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X2)) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq19 (X1 X2 : G) : ((X2 ◇ X1) ◇ X2) = X1 := superpose eq18 eq14 -- backward demodulation 14,18
  have eq28 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq19 eq19 -- superposition 19,19, 19 into 19, unify on (0).2 in 19 and (0).1.1 in 19
  have eq29 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq19 eq13 -- superposition 13,19, 19 into 13, unify on (0).2 in 19 and (0).1.1 in 13
  have eq31 : sK0 ≠ (sK2 ◇ (sK1 ◇ sK2)) := superpose eq29 eq10 -- backward demodulation 10,29
  have eq33 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq29 eq19 -- backward demodulation 19,29
  have eq35 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq29 eq28 -- backward demodulation 28,29
  have eq36 : sK0 ≠ (sK2 ◇ sK2) := superpose eq29 eq31 -- forward demodulation 31,29
  have eq39 (X0 X1 : G) : X0 = X1 := superpose eq33 eq29 -- superposition 29,33, 33 into 29, unify on (0).2 in 33 and (0).1 in 29
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq36 -- superposition 36,35, 35 into 36, unify on (0).2 in 35 and (0).2 in 36
  subsumption eq50 eq39


@[equational_result]
theorem Equation1703_implies_Equation794 (G : Type*) [Magma G] (h : Equation1703 G) : Equation794 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK3 ◇ sK0) ◇ sK3))) := mod_symm nh
  have eq13 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X2 : G) : ((X2 ◇ X1) ◇ X2) = (X1 ◇ ((X2 ◇ X1) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq18 (X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X2)) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq19 (X1 X2 : G) : ((X2 ◇ X1) ◇ X2) = X1 := superpose eq18 eq14 -- backward demodulation 14,18
  have eq24 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq30 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq19 eq13 -- superposition 13,19, 19 into 13, unify on (0).2 in 19 and (0).1.1 in 13
  have eq36 : sK0 ≠ (sK1 ◇ sK0) := superpose eq30 eq24 -- backward demodulation 24,30
  subsumption eq36 eq30


@[equational_result]
theorem Equation1151_implies_Equation689 (G : Type*) [Magma G] (h : Equation1151 G) : Equation689 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK2 ◇ sK0) ◇ sK3))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ ((X3 ◇ X2) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq24 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X2) = X0 := superpose eq16 eq11 -- backward demodulation 11,16
  have eq27 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = (((X3 ◇ X2) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq9 eq24 -- superposition 24,9, 9 into 24, unify on (0).2 in 9 and (0).1.1.1.2 in 24
  have eq34 (X1 X2 X3 : G) : ((X3 ◇ X2) ◇ X1) = X2 := superpose eq24 eq24 -- superposition 24,24, 24 into 24, unify on (0).2 in 24 and (0).1.1.1 in 24
  have eq37 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = X3 := superpose eq12 eq24 -- superposition 24,12, 12 into 24, unify on (0).2 in 12 and (0).1 in 24
  have eq43 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq16 eq27 -- forward demodulation 27,16
  have eq45 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq43 eq16 -- backward demodulation 16,43
  have eq51 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq45 eq10 -- backward demodulation 10,45
  have eq65 (X1 X3 : G) : X1 = X3 := superpose eq34 eq37 -- superposition 37,34, 34 into 37, unify on (0).2 in 34 and (0).1 in 37
  have eq75 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X1 ◇ X0)) := superpose eq37 eq51 -- superposition 51,37, 37 into 51, unify on (0).2 in 37 and (0).2 in 51
  subsumption eq75 eq65


@[equational_result]
theorem Equation2108_implies_Equation2911 (G : Type*) [Magma G] (h : Equation2108 G) : Equation2911 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X3 ◇ X1)) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.2 in 12
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq17 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X0 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq24 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK2) := superpose eq16 eq10 -- backward demodulation 10,16
  have eq27 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq17 eq16 -- backward demodulation 16,17
  have eq29 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X1)) = X3 := superpose eq27 eq14 -- backward demodulation 14,27
  have eq32 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK2) := superpose eq27 eq24 -- backward demodulation 24,27
  have eq34 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq27 eq29 -- forward demodulation 29,27
  subsumption eq32 eq34


@[equational_result]
theorem Equation187_implies_Equation482 (G : Type*) [Magma G] (h : Equation187 G) : Equation482 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ (sK1 ◇ sK1) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq14 (X2 X3 X4 : G) : (X3 ◇ (X4 ◇ X2)) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq20 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq21 (X2 X3 : G) : X2 = X3 := superpose eq9 eq20 -- superposition 20,9, 9 into 20, unify on (0).2 in 9 and (0).1 in 20
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq13 -- superposition 13,20, 20 into 13, unify on (0).2 in 20 and (0).2 in 13
  subsumption eq27 eq21


@[equational_result]
theorem Equation187_implies_Equation2291 (G : Type*) [Magma G] (h : Equation187 G) : Equation2291 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ (sK0 ◇ sK1) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq14 (X2 X3 X4 : G) : (X3 ◇ (X4 ◇ X2)) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq20 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq21 (X2 X3 : G) : X2 = X3 := superpose eq9 eq20 -- superposition 20,9, 9 into 20, unify on (0).2 in 9 and (0).1 in 20
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq13 -- superposition 13,20, 20 into 13, unify on (0).2 in 20 and (0).2 in 13
  subsumption eq27 eq21


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
theorem Equation2703_implies_Equation1324 (G : Type*) [Magma G] (h : Equation2703 G) : Equation1324 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = (((X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X3))) ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X3)) ◇ X4))) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq34 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11, 11 into 13, unify on (0).2 in 11 and (0).2.2.1 in 13
  have eq36 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (((X4 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) ◇ X4) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq50 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq13 eq34 -- superposition 34,13, 13 into 34, unify on (0).2 in 13 and (0).2 in 34
  have eq81 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X3)) ◇ X4))) = X0 := superpose eq50 eq24 -- backward demodulation 24,50
  have eq82 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq50 eq81 -- forward demodulation 81,50
  have eq90 (X0 X1 X2 X4 X5 : G) : ((X4 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = (((X5 ◇ ((X4 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X5) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq134 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ X2) = X0 := superpose eq82 eq82 -- superposition 82,82, 82 into 82, unify on (0).2 in 82 and (0).1.2 in 82
  have eq162 (X0 X1 X2 X4 : G) : ((X4 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = X0 := superpose eq134 eq90 -- backward demodulation 90,134
  have eq163 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X4) := superpose eq162 eq36 -- backward demodulation 36,162
  have eq183 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq82 eq163 -- superposition 163,82, 82 into 163, unify on (0).2 in 82 and (0).1 in 163
  have eq195 (X0 : G) : sK0 ≠ (sK1 ◇ X0) := superpose eq163 eq10 -- superposition 10,163, 163 into 10, unify on (0).2 in 163 and (0).2 in 10
  subsumption eq195 eq183


@[equational_result]
theorem Equation521_implies_Equation2918 (G : Type*) [Magma G] (h : Equation521 G) : Equation2918 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq19 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2) ◇ sK3) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq24 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq40 (X0 : G) : sK0 ≠ (((X0 ◇ (sK0 ◇ sK1)) ◇ sK2) ◇ sK3) := superpose eq15 eq19 -- superposition 19,15, 15 into 19, unify on (0).2 in 15 and (0).2.1.1 in 19
  have eq61 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq87 (X0 X2 X3 : G) : (X3 ◇ (X0 ◇ (X2 ◇ X0))) = X2 := superpose eq61 eq24 -- backward demodulation 24,61
  have eq101 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK3) := superpose eq61 eq40 -- backward demodulation 40,61
  have eq143 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq61 eq87 -- forward demodulation 87,61
  have eq144 (X0 X2 X3 : G) : (X3 ◇ X0) = X2 := superpose eq61 eq143 -- forward demodulation 143,61
  subsumption eq101 eq144


@[equational_result]
theorem Equation521_implies_Equation2903 (G : Type*) [Magma G] (h : Equation521 G) : Equation2903 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq19 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK1) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq24 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq40 (X0 : G) : sK0 ≠ (((X0 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK1) := superpose eq15 eq19 -- superposition 19,15, 15 into 19, unify on (0).2 in 15 and (0).2.1.1 in 19
  have eq61 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq87 (X0 X2 X3 : G) : (X3 ◇ (X0 ◇ (X2 ◇ X0))) = X2 := superpose eq61 eq24 -- backward demodulation 24,61
  have eq101 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq61 eq40 -- backward demodulation 40,61
  have eq143 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X2 := superpose eq61 eq87 -- forward demodulation 87,61
  have eq144 (X0 X2 X3 : G) : (X3 ◇ X0) = X2 := superpose eq61 eq143 -- forward demodulation 143,61
  subsumption eq101 eq144


@[equational_result]
theorem Equation755_implies_Equation677 (G : Type*) [Magma G] (h : Equation755 G) : Equation677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq13 (X1 X2 X4 : G) : (X4 ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X2 X4 : G) : X2 = X4 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq21 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ X0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.2 in 10
  subsumption eq21 eq15


@[equational_result]
theorem Equation755_implies_Equation3025 (G : Type*) [Magma G] (h : Equation755 G) : Equation3025 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X1 X2 X4 : G) : (X4 ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X2 X4 : G) : X2 = X4 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq21 (X0 : G) : sK0 ≠ (X0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq21 eq15


@[equational_result]
theorem Equation538_implies_Equation2772 (G : Type*) [Magma G] (h : Equation538 G) : Equation2772 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X0 ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq18 (X0 X2 X3 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X2))) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq22 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq23 (X0 X2 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := superpose eq14 eq18 -- forward demodulation 18,14
  have eq24 (X0 X2 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ X2) = X0 := superpose eq14 eq23 -- forward demodulation 23,14
  have eq25 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq14 eq24 -- forward demodulation 24,14
  have eq26 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq14 eq25 -- forward demodulation 25,14
  have eq31 : sK0 ≠ (sK0 ◇ sK2) := superpose eq14 eq22 -- forward demodulation 22,14
  subsumption eq31 eq26


@[equational_result]
theorem Equation2112_implies_Equation995 (G : Type*) [Magma G] (h : Equation2112 G) : Equation995 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq25 (X0 X1 : G) : sK0 ≠ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq25 eq17


@[equational_result]
theorem Equation2112_implies_Equation1516 (G : Type*) [Magma G] (h : Equation2112 G) : Equation1516 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq24 (X0 X1 : G) : sK0 ≠ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq24 eq17


@[equational_result]
theorem Equation2112_implies_Equation1286 (G : Type*) [Magma G] (h : Equation2112 G) : Equation1286 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq25 (X0 X1 : G) : sK0 ≠ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq25 eq17


@[equational_result]
theorem Equation1500_implies_Equation1895 (G : Type*) [Magma G] (h : Equation1500 G) : Equation1895 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq15 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq18 (X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq20 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = X1 := superpose eq18 eq14 -- backward demodulation 14,18
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq13 eq20 -- superposition 20,13, 13 into 20, unify on (0).2 in 13 and (0).1.2 in 20
  have eq33 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq15 eq29 -- forward demodulation 29,15
  have eq36 (X1 X2 : G) : (X2 ◇ X2) = X1 := superpose eq33 eq20 -- backward demodulation 20,33
  have eq39 (X1 X2 : G) : X1 = X2 := superpose eq36 eq36 -- superposition 36,36, 36 into 36, unify on (0).2 in 36 and (0).1 in 36
  have eq44 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq36 eq16 -- superposition 16,36, 36 into 16, unify on (0).2 in 36 and (0).2 in 16
  subsumption eq44 eq39


@[equational_result]
theorem Equation1500_implies_Equation498 (G : Type*) [Magma G] (h : Equation1500 G) : Equation498 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := mod_symm nh
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq15 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq17 (X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq18 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq20 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = X1 := superpose eq17 eq14 -- backward demodulation 14,17
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq13 eq20 -- superposition 20,13, 13 into 20, unify on (0).2 in 13 and (0).1.2 in 20
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq15 eq28 -- forward demodulation 28,15
  have eq35 (X1 X2 : G) : (X2 ◇ X2) = X1 := superpose eq32 eq20 -- backward demodulation 20,32
  have eq36 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK3)) := superpose eq32 eq18 -- backward demodulation 18,32
  have eq37 : sK0 ≠ (sK1 ◇ sK3) := superpose eq32 eq36 -- forward demodulation 36,32
  have eq39 (X1 X2 : G) : X1 = X2 := superpose eq35 eq35 -- superposition 35,35, 35 into 35, unify on (0).2 in 35 and (0).1 in 35
  have eq44 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq35 eq37 -- superposition 37,35, 35 into 37, unify on (0).2 in 35 and (0).2 in 37
  subsumption eq44 eq39


@[equational_result]
theorem Equation996_implies_Equation496 (G : Type*) [Magma G] (h : Equation996 G) : Equation496 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X0))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X3 X4 : G) : (X1 ◇ X3) = (X4 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK1 ◇ sK3) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq15 (X3 X4 X5 : G) : (X4 ◇ X5) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq25 (X0 X1 : G) : sK0 ≠ (X0 ◇ X1) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq25 eq15


@[equational_result]
theorem Equation1942_implies_Equation59 (G : Type*) [Magma G] (h : Equation1942 G) : Equation59 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ X3)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq21 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3)) ◇ X2) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq23 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq32 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) ◇ X0) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq34 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3) ◇ X0) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq41 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq32 eq34 -- forward demodulation 34,32
  have eq42 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq41 eq19 -- backward demodulation 19,41
  have eq49 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X2) := superpose eq42 eq21 -- backward demodulation 21,42
  have eq50 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ (X2 ◇ X0)) ◇ X2) := superpose eq42 eq13 -- backward demodulation 13,42
  have eq51 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ X2) := superpose eq23 eq49 -- forward demodulation 49,23
  have eq73 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2)))) = X3 := superpose eq51 eq12 -- superposition 12,51, 51 into 12, unify on (0).2 in 51 and (0).1.1.2 in 12
  have eq79 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := superpose eq51 eq9 -- superposition 9,51, 51 into 9, unify on (0).2 in 51 and (0).1.2 in 9
  have eq117 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X3)) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq50 eq9 -- superposition 9,50, 50 into 9, unify on (0).2 in 50 and (0).1.2 in 9
  have eq141 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq79 eq117 -- forward demodulation 117,79
  have eq142 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq141 eq9 -- backward demodulation 9,141
  have eq145 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ X0)) = X3 := superpose eq141 eq23 -- backward demodulation 23,141
  have eq161 : sK0 ≠ (sK0 ◇ sK2) := superpose eq142 eq10 -- backward demodulation 10,142
  have eq162 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ X0) = X3 := superpose eq145 eq73 -- backward demodulation 73,145
  have eq166 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq145 eq162 -- forward demodulation 162,145
  have eq174 (X1 X2 : G) : X1 = X2 := superpose eq142 eq166 -- superposition 166,142, 142 into 166, unify on (0).2 in 142 and (0).1 in 166
  have eq183 (X0 : G) : sK0 ≠ X0 := superpose eq166 eq161 -- superposition 161,166, 166 into 161, unify on (0).2 in 166 and (0).2 in 161
  subsumption eq183 eq174


@[equational_result]
theorem Equation1942_implies_Equation2914 (G : Type*) [Magma G] (h : Equation1942 G) : Equation2914 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ X3)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq21 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3)) ◇ X2) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq23 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq32 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) ◇ X0) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq34 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3) ◇ X0) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq41 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq32 eq34 -- forward demodulation 34,32
  have eq42 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq41 eq19 -- backward demodulation 19,41
  have eq49 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X2) := superpose eq42 eq21 -- backward demodulation 21,42
  have eq50 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ (X2 ◇ X0)) ◇ X2) := superpose eq42 eq13 -- backward demodulation 13,42
  have eq51 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ X2) := superpose eq23 eq49 -- forward demodulation 49,23
  have eq73 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2)))) = X3 := superpose eq51 eq12 -- superposition 12,51, 51 into 12, unify on (0).2 in 51 and (0).1.1.2 in 12
  have eq79 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := superpose eq51 eq9 -- superposition 9,51, 51 into 9, unify on (0).2 in 51 and (0).1.2 in 9
  have eq117 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X3)) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq50 eq9 -- superposition 9,50, 50 into 9, unify on (0).2 in 50 and (0).1.2 in 9
  have eq141 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq79 eq117 -- forward demodulation 117,79
  have eq142 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq141 eq9 -- backward demodulation 9,141
  have eq145 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ X0)) = X3 := superpose eq141 eq23 -- backward demodulation 23,141
  have eq161 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq142 eq10 -- backward demodulation 10,142
  have eq162 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ X0) = X3 := superpose eq145 eq73 -- backward demodulation 73,145
  have eq166 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq145 eq162 -- forward demodulation 162,145
  have eq169 (X2 X3 : G) : X2 = X3 := superpose eq166 eq166 -- superposition 166,166, 166 into 166, unify on (0).2 in 166 and (0).1 in 166
  have eq177 (X0 : G) : sK0 ≠ (X0 ◇ sK2) := superpose eq166 eq161 -- superposition 161,166, 166 into 161, unify on (0).2 in 166 and (0).2.1 in 161
  subsumption eq177 eq169


@[equational_result]
theorem Equation2729_implies_Equation1942 (G : Type*) [Magma G] (h : Equation2729 G) : Equation1942 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X4 X5 : G) : (((X4 ◇ X5) ◇ X1) ◇ X4) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = (X2 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq38 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq38 eq17


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
theorem Equation2729_implies_Equation1760 (G : Type*) [Magma G] (h : Equation2729 G) : Equation1760 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X1 X4 X5 : G) : (((X4 ◇ X5) ◇ X1) ◇ X4) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = (X2 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq41 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq41 eq17


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
theorem Equation927_implies_Equation3150 (G : Type*) [Magma G] (h : Equation927 G) : Equation3150 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = X1 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq43 (X2 X3 : G) : X2 = X3 := superpose eq16 eq16 -- superposition 16,16, 16 into 16, unify on (0).2 in 16 and (0).1 in 16
  have eq49 (X0 : G) : sK0 ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1.1 in 10
  subsumption eq49 eq43


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
theorem Equation1294_implies_Equation687 (G : Type*) [Magma G] (h : Equation1294 G) : Equation687 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK2 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X4 : G) : X1 = X4 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq19 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ X0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.2 in 10
  subsumption eq19 eq14


@[equational_result]
theorem Equation1294_implies_Equation2500 (G : Type*) [Magma G] (h : Equation1294 G) : Equation2500 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X4 : G) : X1 = X4 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq21 eq14


@[equational_result]
theorem Equation2924_implies_Equation477 (G : Type*) [Magma G] (h : Equation2924 G) : Equation477 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = (((X3 ◇ X1) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X1) ◇ X3) = (((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X4) ◇ X4) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq24 (X1 X2 X3 X4 : G) : ((X3 ◇ ((X1 ◇ X2) ◇ X4)) ◇ X3) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq32 (X0 X1 X3 X4 : G) : ((X3 ◇ X1) ◇ X3) = (X0 ◇ X4) := superpose eq24 eq13 -- backward demodulation 13,24
  have eq73 (X1 X3 X4 : G) : ((X3 ◇ X4) ◇ X3) = X1 := superpose eq9 eq32 -- superposition 32,9, 9 into 32, unify on (0).2 in 9 and (0).2 in 32
  have eq108 (X0 X1 : G) : sK0 ≠ ((X0 ◇ X1) ◇ X0) := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2 in 10
  subsumption eq108 eq73


@[equational_result]
theorem Equation2924_implies_Equation1102 (G : Type*) [Magma G] (h : Equation2924 G) : Equation1102 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = (((X3 ◇ X1) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X1) ◇ X3) = (((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X4) ◇ X4) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq24 (X1 X2 X3 X4 : G) : ((X3 ◇ ((X1 ◇ X2) ◇ X4)) ◇ X3) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq32 (X0 X1 X3 X4 : G) : ((X3 ◇ X1) ◇ X3) = (X0 ◇ X4) := superpose eq24 eq13 -- backward demodulation 13,24
  have eq73 (X1 X3 X4 : G) : ((X3 ◇ X4) ◇ X3) = X1 := superpose eq9 eq32 -- superposition 32,9, 9 into 32, unify on (0).2 in 9 and (0).2 in 32
  have eq108 (X0 X1 : G) : sK0 ≠ ((X0 ◇ X1) ◇ X0) := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2 in 10
  subsumption eq108 eq73


@[equational_result]
theorem Equation2924_implies_Equation1147 (G : Type*) [Magma G] (h : Equation2924 G) : Equation1147 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK0 ◇ sK0)) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = (((X3 ◇ X1) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X1) ◇ X3) = (((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X4) ◇ X4) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq24 (X1 X2 X3 X4 : G) : ((X3 ◇ ((X1 ◇ X2) ◇ X4)) ◇ X3) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq32 (X0 X1 X3 X4 : G) : ((X3 ◇ X1) ◇ X3) = (X0 ◇ X4) := superpose eq24 eq13 -- backward demodulation 13,24
  have eq73 (X1 X3 X4 : G) : ((X3 ◇ X4) ◇ X3) = X1 := superpose eq9 eq32 -- superposition 32,9, 9 into 32, unify on (0).2 in 9 and (0).2 in 32
  have eq108 (X0 X1 : G) : sK0 ≠ ((X0 ◇ X1) ◇ X0) := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2 in 10
  subsumption eq108 eq73


@[equational_result]
theorem Equation2924_implies_Equation3099 (G : Type*) [Magma G] (h : Equation2924 G) : Equation3099 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK3) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = (((X3 ◇ X1) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X1) ◇ X3) = (((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X4) ◇ X4) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq24 (X1 X2 X3 X4 : G) : ((X3 ◇ ((X1 ◇ X2) ◇ X4)) ◇ X3) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq32 (X0 X1 X3 X4 : G) : ((X3 ◇ X1) ◇ X3) = (X0 ◇ X4) := superpose eq24 eq13 -- backward demodulation 13,24
  have eq80 (X0 X1 X3 X4 : G) : ((X3 ◇ X4) ◇ X0) = X1 := superpose eq32 eq9 -- superposition 9,32, 32 into 9, unify on (0).2 in 32 and (0).1.1 in 9
  have eq99 (X0 X1 : G) : sK0 ≠ ((((X0 ◇ X1) ◇ X0) ◇ sK3) ◇ sK2) := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2.1.1 in 10
  subsumption eq99 eq80


@[equational_result]
theorem Equation874_implies_Equation453 (G : Type*) [Magma G] (h : Equation874 G) : Equation453 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X2 : G) : X1 = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq22 (X0 : G) : sK0 ≠ ((X0 ◇ X0) ◇ X0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 eq14


@[equational_result]
theorem Equation874_implies_Equation3114 (G : Type*) [Magma G] (h : Equation874 G) : Equation3114 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK1) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X2 : G) : X1 = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq19 (X0 : G) : sK0 ≠ (((X0 ◇ X0) ◇ X0) ◇ sK2) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq19 eq14


@[equational_result]
theorem Equation979_implies_Equation558 (G : Type*) [Magma G] (h : Equation979 G) : Equation558 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 : G) : (X2 ◇ X3) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq30 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (X0 ◇ X0)))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.2.2 in 10
  subsumption eq30 eq16


@[equational_result]
theorem Equation979_implies_Equation1536 (G : Type*) [Magma G] (h : Equation979 G) : Equation1536 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 : G) : (X2 ◇ X3) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq26 (X0 X1 : G) : sK0 ≠ ((X0 ◇ X1) ◇ (sK2 ◇ (sK0 ◇ sK1))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq26 eq16


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
theorem Equation792_implies_Equation1923 (G : Type*) [Magma G] (h : Equation792 G) : Equation1923 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq13 (X0 X2 X3 X4 : G) : (((X3 ◇ X4) ◇ X0) ◇ X4) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X3 X4 : G) : X3 = X4 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1 in 13
  have eq28 (X0 X1 X2 : G) : sK0 ≠ (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq28 eq20


@[equational_result]
theorem Equation3123_implies_Equation1083 (G : Type*) [Magma G] (h : Equation3123 G) : Equation1083 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq18 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq20 (X0 X1 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq15 eq11 -- backward demodulation 11,15
  have eq21 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq15 eq9 -- backward demodulation 9,15
  have eq22 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X0 := superpose eq18 eq20 -- backward demodulation 20,18
  have eq30 (X0 X2 : G) : X0 = X2 := superpose eq21 eq22 -- superposition 22,21, 21 into 22, unify on (0).2 in 21 and (0).1 in 22
  have eq41 (X0 : G) : sK0 ≠ (sK1 ◇ X0) := superpose eq30 eq14 -- superposition 14,30, 30 into 14, unify on (0).2 in 30 and (0).2.2 in 14
  subsumption eq41 eq30


@[equational_result]
theorem Equation3123_implies_Equation3569 (G : Type*) [Magma G] (h : Equation3123 G) : Equation3569 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq17 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq18 (X0 X1 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq19 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq14 eq9 -- backward demodulation 9,14
  have eq20 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq21 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq18 -- backward demodulation 18,17
  have eq26 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq13 eq21 -- superposition 21,13, 13 into 21, unify on (0).2 in 13 and (0).1.2 in 21
  have eq29 (X0 X2 : G) : X0 = X2 := superpose eq19 eq21 -- superposition 21,19, 19 into 21, unify on (0).2 in 19 and (0).1 in 21
  have eq39 (X0 : G) : (sK0 ◇ sK1) ≠ X0 := superpose eq29 eq20 -- superposition 20,29, 29 into 20, unify on (0).2 in 29 and (0).2 in 20
  subsumption eq39 eq26


@[equational_result]
theorem Equation3123_implies_Equation507 (G : Type*) [Magma G] (h : Equation3123 G) : Equation507 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq17 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq18 (X0 X1 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq19 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq14 eq9 -- backward demodulation 9,14
  have eq20 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq18 -- backward demodulation 18,17
  have eq24 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK2)) := superpose eq20 eq10 -- backward demodulation 10,20
  have eq29 (X0 X2 : G) : X0 = X2 := superpose eq19 eq20 -- superposition 20,19, 19 into 20, unify on (0).2 in 19 and (0).1 in 20
  have eq33 : sK0 ≠ sK1 := superpose eq20 eq24 -- superposition 24,20, 20 into 24, unify on (0).2 in 20 and (0).2 in 24
  subsumption eq33 eq29


@[equational_result]
theorem Equation3123_implies_Equation685 (G : Type*) [Magma G] (h : Equation3123 G) : Equation685 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK3))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq17 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq18 (X0 X1 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq20 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK2)) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq21 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq18 -- backward demodulation 18,17
  have eq33 : sK0 ≠ sK0 := superpose eq21 eq20 -- superposition 20,21, 21 into 20, unify on (0).2 in 21 and (0).2 in 20
  subsumption eq33 rfl


@[equational_result]
theorem Equation2943_implies_Equation3123 (G : Type*) [Magma G] (h : Equation2943 G) : Equation3123 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK2) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 (X2 X3 : G) : X2 = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq25 (X0 X1 : G) : sK0 ≠ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq25 eq18


@[equational_result]
theorem Equation2943_implies_Equation2658 (G : Type*) [Magma G] (h : Equation2943 G) : Equation2658 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 (X2 X3 : G) : X2 = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq27 (X0 X1 : G) : sK0 ≠ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ sK3) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq27 eq18


@[equational_result]
theorem Equation3127_implies_Equation2943 (G : Type*) [Magma G] (h : Equation3127 G) : Equation2943 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK0)) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq23 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X3) ◇ ((X1 ◇ X4) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) ◇ ((X1 ◇ X4) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2.1.1 in 11
  have eq29 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq36 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq29 eq11 -- backward demodulation 11,29
  have eq39 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X3) ◇ ((X1 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2))) ◇ ((X1 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq29 eq23 -- backward demodulation 23,29
  have eq51 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) := superpose eq29 eq10 -- backward demodulation 10,29
  have eq54 (X0 X1 X3 : G) : (((X1 ◇ X3) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := superpose eq29 eq36 -- forward demodulation 36,29
  have eq55 (X0 X1 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ X0) = X0 := superpose eq29 eq54 -- forward demodulation 54,29
  have eq56 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ X0) = X0 := superpose eq29 eq55 -- forward demodulation 55,29
  have eq57 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq29 eq56 -- forward demodulation 56,29
  have eq64 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X3) ◇ (X1 ◇ X4)) ◇ (X1 ◇ X4)) := superpose eq29 eq39 -- forward demodulation 39,29
  have eq65 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X3) ◇ X1) ◇ X1) := superpose eq29 eq64 -- forward demodulation 64,29
  have eq66 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq57 eq65 -- forward demodulation 65,57
  have eq67 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq29 eq66 -- forward demodulation 66,29
  subsumption eq51 eq67


@[equational_result]
theorem Equation3127_implies_Equation447 (G : Type*) [Magma G] (h : Equation3127 G) : Equation447 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq29 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq51 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := superpose eq29 eq10 -- backward demodulation 10,29
  subsumption eq51 eq29


@[equational_result]
theorem Equation3127_implies_Equation683 (G : Type*) [Magma G] (h : Equation3127 G) : Equation683 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq29 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq36 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ ((X0 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := superpose eq29 eq11 -- backward demodulation 11,29
  have eq51 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := superpose eq29 eq10 -- backward demodulation 10,29
  have eq54 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := superpose eq29 eq36 -- forward demodulation 36,29
  have eq55 (X0 X1 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ X0) = X0 := superpose eq29 eq54 -- forward demodulation 54,29
  have eq56 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ X0) = X0 := superpose eq29 eq55 -- forward demodulation 55,29
  have eq57 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq29 eq56 -- forward demodulation 56,29
  have eq102 : sK0 ≠ (sK1 ◇ sK0) := superpose eq29 eq51 -- forward demodulation 51,29
  subsumption eq102 eq57


@[equational_result]
theorem Equation3127_implies_Equation1486 (G : Type*) [Magma G] (h : Equation3127 G) : Equation1486 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq29 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq36 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ ((X0 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := superpose eq29 eq11 -- backward demodulation 11,29
  have eq51 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq29 eq10 -- backward demodulation 10,29
  have eq54 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := superpose eq29 eq36 -- forward demodulation 36,29
  have eq55 (X0 X1 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ X0) = X0 := superpose eq29 eq54 -- forward demodulation 54,29
  have eq56 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ X0) = X0 := superpose eq29 eq55 -- forward demodulation 55,29
  have eq57 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq29 eq56 -- forward demodulation 56,29
  subsumption eq51 eq57


@[equational_result]
theorem Equation3127_implies_Equation2703 (G : Type*) [Magma G] (h : Equation3127 G) : Equation2703 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2 in 12
  have eq19 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq30 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq15 eq19 -- superposition 19,15, 15 into 19, unify on (0).2 in 15 and (0).2 in 19
  have eq62 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq74 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ ((X0 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := superpose eq62 eq11 -- backward demodulation 11,62
  have eq104 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq62 eq30 -- backward demodulation 30,62
  have eq109 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := superpose eq62 eq74 -- forward demodulation 74,62
  have eq110 (X0 X1 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ X0) = X0 := superpose eq62 eq109 -- forward demodulation 109,62
  have eq111 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ X0) = X0 := superpose eq62 eq110 -- forward demodulation 110,62
  have eq112 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq62 eq111 -- forward demodulation 111,62
  subsumption eq104 eq112


@[equational_result]
theorem Equation3127_implies_Equation1888 (G : Type*) [Magma G] (h : Equation3127 G) : Equation1888 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq29 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq35 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X1) = X0 := superpose eq29 eq9 -- backward demodulation 9,29
  have eq51 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := superpose eq29 eq10 -- backward demodulation 10,29
  have eq52 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq29 eq35 -- forward demodulation 35,29
  have eq53 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq29 eq52 -- forward demodulation 52,29
  have eq102 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq29 eq51 -- forward demodulation 51,29
  have eq103 : sK0 ≠ (sK1 ◇ sK1) := superpose eq29 eq102 -- forward demodulation 102,29
  subsumption eq103 eq53


@[equational_result]
theorem Equation3127_implies_Equation1896 (G : Type*) [Magma G] (h : Equation3127 G) : Equation1896 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq29 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq36 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ ((X0 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := superpose eq29 eq11 -- backward demodulation 11,29
  have eq51 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq29 eq10 -- backward demodulation 10,29
  have eq54 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := superpose eq29 eq36 -- forward demodulation 36,29
  have eq55 (X0 X1 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ X0) = X0 := superpose eq29 eq54 -- forward demodulation 54,29
  have eq56 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ X0) = X0 := superpose eq29 eq55 -- forward demodulation 55,29
  have eq57 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq29 eq56 -- forward demodulation 56,29
  subsumption eq51 eq57


@[equational_result]
theorem Equation3127_implies_Equation2895 (G : Type*) [Magma G] (h : Equation3127 G) : Equation2895 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK3) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq29 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq51 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) := superpose eq29 eq10 -- backward demodulation 10,29
  have eq102 : sK0 ≠ (sK0 ◇ sK1) := superpose eq29 eq51 -- forward demodulation 51,29
  subsumption eq102 eq29


@[equational_result]
theorem Equation2920_implies_Equation1487 (G : Type*) [Magma G] (h : Equation2920 G) : Equation1487 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.2 in 13
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2.2 in 13
  have eq20 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X3) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X4)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1))) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq33 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).1.2.2 in 13
  have eq38 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1))) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.1 in 17
  have eq52 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq16 eq38 -- forward demodulation 38,16
  have eq56 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X0 ◇ X3) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X4)))) = X0 := superpose eq52 eq20 -- backward demodulation 20,52
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1) = X0 := superpose eq52 eq9 -- backward demodulation 9,52
  have eq61 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq52 eq16 -- backward demodulation 16,52
  have eq67 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X3) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4)))) = X0 := superpose eq52 eq56 -- forward demodulation 56,52
  have eq68 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq33 eq61 -- forward demodulation 61,33
  have eq71 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq68 eq58 -- backward demodulation 58,68
  have eq72 (X0 X1 X3 X4 : G) : (X1 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X3) ◇ ((X1 ◇ X1) ◇ X4)))) = X0 := superpose eq68 eq67 -- backward demodulation 67,68
  have eq83 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK2) := superpose eq68 eq10 -- backward demodulation 10,68
  have eq84 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq71 eq72 -- forward demodulation 72,71
  have eq97 (X0 X1 : G) : X0 = X1 := superpose eq17 eq84 -- superposition 84,17, 17 into 84, unify on (0).2 in 17 and (0).1 in 84
  have eq106 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq84 eq83 -- superposition 83,84, 84 into 83, unify on (0).2 in 84 and (0).2 in 83
  subsumption eq106 eq97


