import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation895_implies_Equation1670 (G : Type*) [Magma G] (h : Equation895 G) : Equation1670 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq28 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2.2 in 11
  have eq29 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq38 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.2 in 9
  have eq58 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X2) = X3 := superpose eq17 eq29 -- superposition 29,17, 17 into 29, unify on (0).2 in 17 and (0).1.1.2.1 in 29
  have eq83 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) := superpose eq29 eq9 -- superposition 9,29, 29 into 9, unify on (0).2 in 29 and (0).1.2 in 9
  have eq87 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2) = X3 := superpose eq17 eq58 -- forward demodulation 58,17
  have eq88 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X3 := superpose eq38 eq87 -- forward demodulation 87,38
  have eq89 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq88 eq10 -- backward demodulation 10,88
  have eq94 (X0 X2 X4 : G) : (X4 ◇ (X0 ◇ (X4 ◇ X2))) = (X2 ◇ X0) := superpose eq83 eq28 -- backward demodulation 28,83
  have eq173 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := superpose eq38 eq11 -- superposition 11,38, 38 into 11, unify on (0).2 in 38 and (0).1.2.2 in 11
  have eq178 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3)) = X2 := superpose eq38 eq12 -- superposition 12,38, 38 into 12, unify on (0).2 in 38 and (0).1.2.1.2.2 in 12
  have eq187 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X0 ◇ (X2 ◇ X1)) := superpose eq38 eq94 -- superposition 94,38, 38 into 94, unify on (0).2 in 38 and (0).1.2.2 in 94
  have eq235 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X3 ◇ X2))) = X2 := superpose eq187 eq178 -- backward demodulation 178,187
  have eq394 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X3 ◇ X2) ◇ (X3 ◇ (X1 ◇ X0))))) = X2 := superpose eq187 eq235 -- forward demodulation 235,187
  have eq395 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)))) = X2 := superpose eq187 eq394 -- forward demodulation 394,187
  have eq396 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq88 eq395 -- forward demodulation 395,88
  have eq397 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq94 eq396 -- forward demodulation 396,94
  have eq398 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq397 eq173 -- backward demodulation 173,397
  have eq1092 : sK0 ≠ sK0 := superpose eq398 eq89 -- superposition 89,398, 398 into 89, unify on (0).2 in 398 and (0).2 in 89
  subsumption eq1092 rfl


@[equational_result]
theorem Equation895_implies_Equation2064 (G : Type*) [Magma G] (h : Equation895 G) : Equation2064 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.2 in 12
  have eq28 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2.2 in 11
  have eq29 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq39 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.2 in 9
  have eq59 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X2) = X3 := superpose eq17 eq29 -- superposition 29,17, 17 into 29, unify on (0).2 in 17 and (0).1.1.2.1 in 29
  have eq84 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) := superpose eq29 eq9 -- superposition 9,29, 29 into 9, unify on (0).2 in 29 and (0).1.2 in 9
  have eq88 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2) = X3 := superpose eq17 eq59 -- forward demodulation 59,17
  have eq89 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X3 := superpose eq39 eq88 -- forward demodulation 88,39
  have eq93 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq84 eq26 -- backward demodulation 26,84
  have eq94 (X0 X2 X4 : G) : (X4 ◇ (X0 ◇ (X4 ◇ X2))) = (X2 ◇ X0) := superpose eq84 eq28 -- backward demodulation 28,84
  have eq127 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) ◇ X2) ◇ X4) ◇ (X1 ◇ X4)) = X0 := superpose eq12 eq93 -- superposition 93,12, 12 into 93, unify on (0).2 in 12 and (0).1.2.1 in 93
  have eq178 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3)) = X2 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.2.1.2.2 in 12
  have eq187 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X0 ◇ (X2 ◇ X1)) := superpose eq39 eq94 -- superposition 94,39, 39 into 94, unify on (0).2 in 39 and (0).1.2.2 in 94
  have eq228 (X0 X1 X2 X3 X4 : G) : (((((X2 ◇ X3) ◇ (X0 ◇ X3)) ◇ (X2 ◇ X1)) ◇ X4) ◇ (X1 ◇ X4)) = X0 := superpose eq187 eq127 -- backward demodulation 127,187
  have eq235 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X3 ◇ X2))) = X2 := superpose eq187 eq178 -- backward demodulation 178,187
  have eq265 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)) := superpose eq187 eq10 -- backward demodulation 10,187
  have eq351 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X1) ◇ (X4 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3)))) ◇ (X1 ◇ X4)) = X0 := superpose eq187 eq228 -- forward demodulation 228,187
  have eq352 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X4 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) ◇ X2)) ◇ (X1 ◇ X4)) = X0 := superpose eq187 eq351 -- forward demodulation 351,187
  have eq353 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ (X0 ◇ X3)) ◇ (X2 ◇ X4))) ◇ (X1 ◇ X4)) = X0 := superpose eq187 eq352 -- forward demodulation 352,187
  have eq354 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X3) ◇ ((X2 ◇ X4) ◇ (X2 ◇ X3)))) ◇ (X1 ◇ X4)) = X0 := superpose eq187 eq353 -- forward demodulation 353,187
  have eq355 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X3 ◇ (((X2 ◇ X4) ◇ (X2 ◇ X3)) ◇ X0))) ◇ (X1 ◇ X4)) = X0 := superpose eq187 eq354 -- forward demodulation 354,187
  have eq356 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X3 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X2 ◇ X4))))) ◇ (X1 ◇ X4)) = X0 := superpose eq187 eq355 -- forward demodulation 355,187
  have eq357 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X3 ◇ (X3 ◇ ((X0 ◇ (X2 ◇ X4)) ◇ X2)))) ◇ (X1 ◇ X4)) = X0 := superpose eq187 eq356 -- forward demodulation 356,187
  have eq358 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X3 ◇ (X3 ◇ ((X2 ◇ X4) ◇ (X2 ◇ X0))))) ◇ (X1 ◇ X4)) = X0 := superpose eq187 eq357 -- forward demodulation 357,187
  have eq359 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X3 ◇ (X3 ◇ (X4 ◇ ((X2 ◇ X0) ◇ X2))))) ◇ (X1 ◇ X4)) = X0 := superpose eq187 eq358 -- forward demodulation 358,187
  have eq360 (X0 X1 X3 X4 : G) : ((X1 ◇ (X3 ◇ (X3 ◇ (X4 ◇ X0)))) ◇ (X1 ◇ X4)) = X0 := superpose eq89 eq359 -- forward demodulation 359,89
  have eq395 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X3 ◇ X2) ◇ (X3 ◇ (X1 ◇ X0))))) = X2 := superpose eq187 eq235 -- forward demodulation 235,187
  have eq396 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)))) = X2 := superpose eq187 eq395 -- forward demodulation 395,187
  have eq397 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq89 eq396 -- forward demodulation 396,89
  have eq398 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq94 eq397 -- forward demodulation 397,94
  have eq405 (X0 X1 X4 : G) : ((X1 ◇ (X4 ◇ X0)) ◇ (X1 ◇ X4)) = X0 := superpose eq398 eq360 -- backward demodulation 360,398
  subsumption eq265 eq405


@[equational_result]
theorem Equation895_implies_Equation508 (G : Type*) [Magma G] (h : Equation895 G) : Equation508 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq20 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq22 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1.2.2 in 11
  have eq52 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2.2 in 11
  have eq53 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq56 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq22 eq22 -- superposition 22,22, 22 into 22, unify on (0).2 in 22 and (0).1.2 in 22
  have eq57 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq17 eq22 -- superposition 22,17, 17 into 22, unify on (0).2 in 17 and (0).1.2 in 22
  have eq93 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq22 eq53 -- superposition 53,22, 22 into 53, unify on (0).2 in 22 and (0).1.1 in 53
  have eq108 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X4) ◇ ((X5 ◇ X3) ◇ X4))) = (X2 ◇ (X5 ◇ X0)) := superpose eq53 eq12 -- superposition 12,53, 53 into 12, unify on (0).2 in 53 and (0).1.2.1 in 12
  have eq122 (X0 X2 X4 : G) : (X2 ◇ X0) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq93 eq52 -- backward demodulation 52,93
  have eq142 (X0 X1 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X5) := superpose eq93 eq108 -- forward demodulation 108,93
  have eq148 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X1 ◇ X0) := superpose eq9 eq56 -- superposition 56,9, 9 into 56, unify on (0).2 in 9 and (0).1.1 in 56
  have eq197 (X0 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = ((X0 ◇ X2) ◇ X5) := superpose eq148 eq142 -- backward demodulation 142,148
  have eq321 (X0 X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq122 eq57 -- superposition 57,122, 122 into 57, unify on (0).2 in 122 and (0).1 in 57
  have eq330 (X0 X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq197 eq321 -- forward demodulation 321,197
  have eq331 (X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ X1) := superpose eq22 eq330 -- forward demodulation 330,22
  have eq332 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq331 eq20 -- backward demodulation 20,331
  subsumption eq332 eq22


@[equational_result]
theorem Equation895_implies_Equation2282 (G : Type*) [Magma G] (h : Equation895 G) : Equation2282 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq20 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq22 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1.2.2 in 11
  have eq52 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2.2 in 11
  have eq53 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq56 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq22 eq22 -- superposition 22,22, 22 into 22, unify on (0).2 in 22 and (0).1.2 in 22
  have eq69 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3)) = X2 := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.2.1.2.2 in 12
  have eq93 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq22 eq53 -- superposition 53,22, 22 into 53, unify on (0).2 in 22 and (0).1.1 in 53
  have eq108 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X4) ◇ ((X5 ◇ X3) ◇ X4))) = (X2 ◇ (X5 ◇ X0)) := superpose eq53 eq12 -- superposition 12,53, 53 into 12, unify on (0).2 in 53 and (0).1.2.1 in 12
  have eq122 (X0 X2 X4 : G) : (X2 ◇ X0) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq93 eq52 -- backward demodulation 52,93
  have eq142 (X0 X1 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X5) := superpose eq93 eq108 -- forward demodulation 108,93
  have eq148 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X1 ◇ X0) := superpose eq9 eq56 -- superposition 56,9, 9 into 56, unify on (0).2 in 9 and (0).1.1 in 56
  have eq197 (X0 X2 X5 : G) : (X2 ◇ (X5 ◇ X0)) = ((X0 ◇ X2) ◇ X5) := superpose eq148 eq142 -- backward demodulation 142,148
  have eq222 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X3 ◇ X2))) = X2 := superpose eq197 eq69 -- backward demodulation 69,197
  have eq232 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X3 ◇ X2) ◇ (X3 ◇ (X1 ◇ X0))))) = X2 := superpose eq197 eq222 -- forward demodulation 222,197
  have eq233 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)))) = X2 := superpose eq197 eq232 -- forward demodulation 232,197
  have eq234 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq56 eq233 -- forward demodulation 233,56
  have eq235 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq122 eq234 -- forward demodulation 234,122
  have eq348 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq197 eq20 -- superposition 20,197, 197 into 20, unify on (0).2 in 197 and (0).2 in 20
  subsumption eq348 eq235


@[equational_result]
theorem Equation895_implies_Equation455 (G : Type*) [Magma G] (h : Equation895 G) : Equation455 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := mod_symm nh
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
  have eq286 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X3 ◇ X2) ◇ (X3 ◇ (X1 ◇ X0))))) = X2 := superpose eq235 eq258 -- forward demodulation 258,235
  have eq287 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)))) = X2 := superpose eq235 eq286 -- forward demodulation 286,235
  have eq288 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq88 eq287 -- forward demodulation 287,88
  have eq289 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq93 eq288 -- forward demodulation 288,93
  have eq291 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq289 eq10 -- backward demodulation 10,289
  subsumption eq291 eq17


@[equational_result]
theorem Equation895_implies_Equation2101 (G : Type*) [Magma G] (h : Equation895 G) : Equation2101 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq29 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq39 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.2 in 9
  have eq59 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X2) = X3 := superpose eq17 eq29 -- superposition 29,17, 17 into 29, unify on (0).2 in 17 and (0).1.1.2.1 in 29
  have eq88 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2) = X3 := superpose eq17 eq59 -- forward demodulation 59,17
  have eq89 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X3 := superpose eq39 eq88 -- forward demodulation 88,39
  have eq90 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq89 eq10 -- backward demodulation 10,89
  subsumption eq90 eq17


@[equational_result]
theorem Equation895_implies_Equation2186 (G : Type*) [Magma G] (h : Equation895 G) : Equation2186 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK1) ◇ (sK2 ◇ sK0)) := mod_symm nh
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
  have eq87 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2) = X3 := superpose eq17 eq58 -- forward demodulation 58,17
  have eq88 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X3 := superpose eq36 eq87 -- forward demodulation 87,36
  have eq89 : sK0 ≠ (sK2 ◇ (sK2 ◇ sK0)) := superpose eq88 eq10 -- backward demodulation 10,88
  have eq93 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ ((X4 ◇ X2) ◇ X0)) = X4 := superpose eq77 eq26 -- backward demodulation 26,77
  have eq94 (X0 X2 X4 : G) : (X2 ◇ X0) = (X4 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq77 eq33 -- backward demodulation 33,77
  have eq102 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq93 eq73 -- backward demodulation 73,93
  have eq189 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X0 ◇ (X2 ◇ X1)) := superpose eq36 eq94 -- superposition 94,36, 36 into 94, unify on (0).2 in 36 and (0).2.2.2 in 94
  have eq708 (X0 X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq94 eq102 -- superposition 102,94, 94 into 102, unify on (0).2 in 94 and (0).1 in 102
  have eq721 (X0 X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq189 eq708 -- forward demodulation 708,189
  have eq722 (X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ X1) := superpose eq36 eq721 -- forward demodulation 721,36
  have eq723 : sK0 ≠ (sK2 ◇ (sK0 ◇ sK2)) := superpose eq722 eq89 -- backward demodulation 89,722
  subsumption eq723 eq36


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
theorem Equation2821_implies_Equation2601 (G : Type*) [Magma G] (h : Equation2821 G) : Equation2601 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK2) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X5)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X3 X4 : G) : ((X3 ◇ X4) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X3 : G) : (X3 ◇ X3) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq19 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq19 eq11


@[equational_result]
theorem Equation2821_implies_Equation2550 (G : Type*) [Magma G] (h : Equation2821 G) : Equation2550 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK2) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X5)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation2821_implies_Equation2618 (G : Type*) [Magma G] (h : Equation2821 G) : Equation2618 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK3) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X5)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq26 rfl


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
theorem Equation2601_implies_Equation2669 (G : Type*) [Magma G] (h : Equation2601 G) : Equation2669 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq22 : sK0 ≠ sK0 := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation3494_implies_Equation3480 (G : Type*) [Magma G] (h : Equation3494 G) : Equation3480 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK0 ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq16 (X1 X3 X5 : G) : (X1 ◇ X1) = (X5 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3494_implies_Equation3488 (G : Type*) [Magma G] (h : Equation3494 G) : Equation3488 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq16 (X1 X3 X5 : G) : (X1 ◇ X1) = (X5 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3494_implies_Equation3503 (G : Type*) [Magma G] (h : Equation3494 G) : Equation3503 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ sK0)) := mod_symm nh
  have eq16 (X1 X3 X5 : G) : (X1 ◇ X1) = (X5 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3494_implies_Equation3507 (G : Type*) [Magma G] (h : Equation3494 G) : Equation3507 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ sK4)) := mod_symm nh
  have eq16 (X1 X3 X5 : G) : (X1 ◇ X1) = (X5 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3494_implies_Equation3476 (G : Type*) [Magma G] (h : Equation3494 G) : Equation3476 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq16 (X1 X3 X5 : G) : (X1 ◇ X1) = (X5 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3494_implies_Equation3495 (G : Type*) [Magma G] (h : Equation3494 G) : Equation3495 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq16 (X1 X3 X5 : G) : (X1 ◇ X1) = (X5 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3480_implies_Equation3494 (G : Type*) [Magma G] (h : Equation3480 G) : Equation3494 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X2) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ sK3)) := mod_symm nh
  have eq16 (X0 X2 X5 : G) : (X0 ◇ X0) = (X5 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X3 : G) : (X1 ◇ X1) = (X3 ◇ X3) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3480_implies_Equation3490 (G : Type*) [Magma G] (h : Equation3480 G) : Equation3490 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X2) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq16 (X0 X2 X5 : G) : (X0 ◇ X0) = (X5 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X3 : G) : (X1 ◇ X1) = (X3 ◇ X3) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq51 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq51 eq27


@[equational_result]
theorem Equation3480_implies_Equation3506 (G : Type*) [Magma G] (h : Equation3480 G) : Equation3506 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X2) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ sK3)) := mod_symm nh
  have eq16 (X0 X2 X5 : G) : (X0 ◇ X0) = (X5 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X3 : G) : (X1 ◇ X1) = (X3 ◇ X3) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation4532_implies_Equation4560 (G : Type*) [Magma G] (h : Equation4532 G) : Equation4560 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK0) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (X3 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X1)) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK3 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq36 (X0 X1 : G) : (X1 ◇ (sK3 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).1 in 16
  have eq44 (X1 : G) : ((sK3 ◇ sK0) ◇ sK3) ≠ (X1 ◇ (sK1 ◇ sK2)) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).1 in 36
  have eq122 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X3) ◇ X2) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq131 (X0 X1 : G) : ((sK3 ◇ sK0) ◇ sK3) ≠ ((X0 ◇ X1) ◇ X0) := superpose eq17 eq44 -- superposition 44,17, 17 into 44, unify on (0).2 in 17 and (0).2 in 44
  subsumption eq131 eq122


@[equational_result]
theorem Equation4532_implies_Equation4446 (G : Type*) [Magma G] (h : Equation4532 G) : Equation4446 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (X3 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X1)) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq34 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK0)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).1 in 16
  have eq120 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = (X4 ◇ (X2 ◇ X3)) := superpose eq14 eq17 -- superposition 17,14, 14 into 17, unify on (0).2 in 14 and (0).2 in 17
  have eq133 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) ≠ (X2 ◇ (sK1 ◇ sK0)) := superpose eq17 eq34 -- superposition 34,17, 17 into 34, unify on (0).2 in 17 and (0).1 in 34
  subsumption eq133 eq120


@[equational_result]
theorem Equation4532_implies_Equation4575 (G : Type*) [Magma G] (h : Equation4532 G) : Equation4575 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK3) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (X3 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X1)) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK3 ◇ sK3)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq34 (X0 X1 : G) : (X1 ◇ (sK3 ◇ sK3)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).1 in 16
  have eq44 (X1 : G) : ((sK3 ◇ sK3) ◇ sK3) ≠ (X1 ◇ (sK1 ◇ sK2)) := superpose eq9 eq34 -- superposition 34,9, 9 into 34, unify on (0).2 in 9 and (0).1 in 34
  have eq122 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X3) ◇ X2) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq134 (X0 X1 : G) : ((sK3 ◇ sK3) ◇ sK3) ≠ ((X0 ◇ X1) ◇ X0) := superpose eq17 eq44 -- superposition 44,17, 17 into 44, unify on (0).2 in 17 and (0).2 in 44
  subsumption eq134 eq122


@[equational_result]
theorem Equation4532_implies_Equation4409 (G : Type*) [Magma G] (h : Equation4532 G) : Equation4409 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (X3 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X1)) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq34 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).1 in 16
  have eq44 (X1 : G) : ((sK1 ◇ sK1) ◇ sK1) ≠ (X1 ◇ (sK0 ◇ sK1)) := superpose eq9 eq34 -- superposition 34,9, 9 into 34, unify on (0).2 in 9 and (0).1 in 34
  have eq122 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X3) ◇ X2) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq134 (X0 X1 : G) : ((sK1 ◇ sK1) ◇ sK1) ≠ ((X0 ◇ X1) ◇ X0) := superpose eq17 eq44 -- superposition 44,17, 17 into 44, unify on (0).2 in 17 and (0).2 in 44
  subsumption eq134 eq122


@[equational_result]
theorem Equation4532_implies_Equation4565 (G : Type*) [Magma G] (h : Equation4532 G) : Equation4565 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK1) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (X3 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X1)) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK3 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq36 (X0 X1 : G) : (X1 ◇ (sK3 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).1 in 16
  have eq44 (X1 : G) : ((sK3 ◇ sK1) ◇ sK3) ≠ (X1 ◇ (sK1 ◇ sK2)) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).1 in 36
  have eq122 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X3) ◇ X2) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq131 (X0 X1 : G) : ((sK3 ◇ sK1) ◇ sK3) ≠ ((X0 ◇ X1) ◇ X0) := superpose eq17 eq44 -- superposition 44,17, 17 into 44, unify on (0).2 in 17 and (0).2 in 44
  subsumption eq131 eq122


@[equational_result]
theorem Equation4532_implies_Equation4449 (G : Type*) [Magma G] (h : Equation4532 G) : Equation4449 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK1 ◇ sK2) ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (X3 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X1)) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).1 in 10
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq36 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK0)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).1 in 16
  have eq120 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = (X4 ◇ (X2 ◇ X3)) := superpose eq14 eq17 -- superposition 17,14, 14 into 17, unify on (0).2 in 14 and (0).2 in 17
  have eq130 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) ≠ (X2 ◇ (sK1 ◇ sK0)) := superpose eq17 eq36 -- superposition 36,17, 17 into 36, unify on (0).2 in 17 and (0).1 in 36
  subsumption eq130 eq120


@[equational_result]
theorem Equation4532_implies_Equation4480 (G : Type*) [Magma G] (h : Equation4532 G) : Equation4480 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (X3 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X1)) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq36 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).1 in 16
  have eq118 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = (X4 ◇ (X2 ◇ X3)) := superpose eq14 eq17 -- superposition 17,14, 14 into 17, unify on (0).2 in 14 and (0).2 in 17
  have eq128 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) ≠ (X2 ◇ (sK1 ◇ sK1)) := superpose eq17 eq36 -- superposition 36,17, 17 into 36, unify on (0).2 in 17 and (0).1 in 36
  subsumption eq128 eq118


@[equational_result]
theorem Equation4532_implies_Equation4546 (G : Type*) [Magma G] (h : Equation4532 G) : Equation4546 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (X3 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X1)) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK2 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq36 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).1 in 16
  have eq44 (X1 : G) : ((sK2 ◇ sK1) ◇ sK2) ≠ (X1 ◇ (sK1 ◇ sK2)) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).1 in 36
  have eq122 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X3) ◇ X2) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq131 (X0 X1 : G) : ((sK2 ◇ sK1) ◇ sK2) ≠ ((X0 ◇ X1) ◇ X0) := superpose eq17 eq44 -- superposition 44,17, 17 into 44, unify on (0).2 in 17 and (0).2 in 44
  subsumption eq131 eq122


@[equational_result]
theorem Equation4532_implies_Equation4503 (G : Type*) [Magma G] (h : Equation4532 G) : Equation4503 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (X3 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X1)) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK3)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq36 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK3)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).1 in 16
  have eq44 (X1 : G) : ((sK2 ◇ sK3) ◇ sK2) ≠ (X1 ◇ (sK1 ◇ sK1)) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).1 in 36
  have eq122 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq131 (X0 X1 : G) : ((sK2 ◇ sK3) ◇ sK2) ≠ ((X0 ◇ X1) ◇ X0) := superpose eq17 eq44 -- superposition 44,17, 17 into 44, unify on (0).2 in 17 and (0).2 in 44
  subsumption eq131 eq122


@[equational_result]
theorem Equation4532_implies_Equation4499 (G : Type*) [Magma G] (h : Equation4532 G) : Equation4499 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (X3 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X1)) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq34 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).1 in 16
  have eq44 (X1 : G) : ((sK2 ◇ sK2) ◇ sK2) ≠ (X1 ◇ (sK1 ◇ sK1)) := superpose eq9 eq34 -- superposition 34,9, 9 into 34, unify on (0).2 in 9 and (0).1 in 34
  have eq122 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X3) ◇ X2) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq134 (X0 X1 : G) : ((sK2 ◇ sK2) ◇ sK2) ≠ ((X0 ◇ X1) ◇ X0) := superpose eq17 eq44 -- superposition 44,17, 17 into 44, unify on (0).2 in 17 and (0).2 in 44
  subsumption eq134 eq122


@[equational_result]
theorem Equation4532_implies_Equation4417 (G : Type*) [Magma G] (h : Equation4532 G) : Equation4417 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (X3 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X1)) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq36 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK0)) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).1 in 16
  have eq44 (X1 : G) : ((sK2 ◇ sK0) ◇ sK2) ≠ (X1 ◇ (sK0 ◇ sK1)) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).1 in 36
  have eq122 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X3) ◇ X2) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq131 (X0 X1 : G) : ((sK2 ◇ sK0) ◇ sK2) ≠ ((X0 ◇ X1) ◇ X0) := superpose eq17 eq44 -- superposition 44,17, 17 into 44, unify on (0).2 in 17 and (0).2 in 44
  subsumption eq131 eq122


@[equational_result]
theorem Equation4532_implies_Equation4486 (G : Type*) [Magma G] (h : Equation4532 G) : Equation4486 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : ((sK1 ◇ sK2) ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (X3 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X1)) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq16 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).1 in 10
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq36 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).1 in 16
  have eq120 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = (X4 ◇ (X2 ◇ X3)) := superpose eq14 eq17 -- superposition 17,14, 14 into 17, unify on (0).2 in 14 and (0).2 in 17
  have eq130 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) ≠ (X2 ◇ (sK1 ◇ sK1)) := superpose eq17 eq36 -- superposition 36,17, 17 into 36, unify on (0).2 in 17 and (0).1 in 36
  subsumption eq130 eq120


@[equational_result]
theorem Equation4560_implies_Equation4532 (G : Type*) [Magma G] (h : Equation4560 G) : Equation4532 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ X4)) = ((X5 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq17 (X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ X3)) = (X1 ◇ (X4 ◇ X5)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (X0 ◇ X1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq128 (X0 X3 X4 X5 X6 X7 : G) : (X3 ◇ (X6 ◇ X7)) = ((X0 ◇ (X4 ◇ X5)) ◇ X0) := superpose eq17 eq14 -- superposition 14,17, 17 into 14, unify on (0).2 in 17 and (0).2.1 in 14
  have eq156 (X2 X3 X4 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((X2 ◇ ((X3 ◇ X4) ◇ sK2)) ◇ X2) := superpose eq14 eq19 -- superposition 19,14, 14 into 19, unify on (0).2 in 14 and (0).2 in 19
  subsumption eq156 eq128


@[equational_result]
theorem Equation4560_implies_Equation4472 (G : Type*) [Magma G] (h : Equation4560 G) : Equation4472 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ X4)) = ((X5 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq17 (X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ X3)) = (X1 ◇ (X4 ◇ X5)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (X0 ◇ X1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq128 (X0 X3 X4 X5 X6 X7 : G) : (X3 ◇ (X6 ◇ X7)) = ((X0 ◇ (X4 ◇ X5)) ◇ X0) := superpose eq17 eq14 -- superposition 14,17, 17 into 14, unify on (0).2 in 17 and (0).2.1 in 14
  have eq156 (X2 X3 X4 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((X2 ◇ ((X3 ◇ X4) ◇ sK1)) ◇ X2) := superpose eq14 eq19 -- superposition 19,14, 14 into 19, unify on (0).2 in 14 and (0).2 in 19
  subsumption eq156 eq128


@[equational_result]
theorem Equation4560_implies_Equation4554 (G : Type*) [Magma G] (h : Equation4560 G) : Equation4554 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ X4)) = ((X5 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq17 (X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ X3)) = (X1 ◇ (X4 ◇ X5)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (X0 ◇ X1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq128 (X0 X3 X4 X5 X6 X7 : G) : (X3 ◇ (X6 ◇ X7)) = ((X0 ◇ (X4 ◇ X5)) ◇ X0) := superpose eq17 eq14 -- superposition 14,17, 17 into 14, unify on (0).2 in 17 and (0).2.1 in 14
  have eq156 (X2 X3 X4 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((X2 ◇ ((X3 ◇ X4) ◇ sK3)) ◇ X2) := superpose eq14 eq19 -- superposition 19,14, 14 into 19, unify on (0).2 in 14 and (0).2 in 19
  subsumption eq156 eq128


@[equational_result]
theorem Equation4560_implies_Equation4514 (G : Type*) [Magma G] (h : Equation4560 G) : Equation4514 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ X4)) = ((X5 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq17 (X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ X3)) = (X1 ◇ (X4 ◇ X5)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (X0 ◇ X1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq128 (X0 X3 X4 X5 X6 X7 : G) : (X3 ◇ (X6 ◇ X7)) = ((X0 ◇ (X4 ◇ X5)) ◇ X0) := superpose eq17 eq14 -- superposition 14,17, 17 into 14, unify on (0).2 in 17 and (0).2.1 in 14
  have eq156 (X2 X3 X4 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((X2 ◇ ((X3 ◇ X4) ◇ sK2)) ◇ X2) := superpose eq14 eq19 -- superposition 19,14, 14 into 19, unify on (0).2 in 14 and (0).2 in 19
  subsumption eq156 eq128


@[equational_result]
theorem Equation4560_implies_Equation4550 (G : Type*) [Magma G] (h : Equation4560 G) : Equation4550 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ X4)) = ((X5 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq17 (X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ X3)) = (X1 ◇ (X4 ◇ X5)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (X0 ◇ X1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq128 (X0 X3 X4 X5 X6 X7 : G) : (X3 ◇ (X6 ◇ X7)) = ((X0 ◇ (X4 ◇ X5)) ◇ X0) := superpose eq17 eq14 -- superposition 14,17, 17 into 14, unify on (0).2 in 17 and (0).2.1 in 14
  have eq146 (X2 X3 X4 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((X2 ◇ ((X3 ◇ X4) ◇ sK2)) ◇ X2) := superpose eq14 eq19 -- superposition 19,14, 14 into 19, unify on (0).2 in 14 and (0).2 in 19
  subsumption eq146 eq128


@[equational_result]
theorem Equation4527_implies_Equation4548 (G : Type*) [Magma G] (h : Equation4527 G) : Equation4548 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq226 (X0 X1 X2 X4 : G) : (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) = (X0 ◇ (X1 ◇ X4)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2 in 12
  have eq276 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ sK0) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2 in 18
  subsumption eq276 eq226


@[equational_result]
theorem Equation4527_implies_Equation4497 (G : Type*) [Magma G] (h : Equation4527 G) : Equation4497 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq226 (X0 X1 X2 X4 : G) : (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) = (X0 ◇ (X1 ◇ X4)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2 in 12
  have eq276 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ sK0) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2 in 18
  subsumption eq276 eq226


@[equational_result]
theorem Equation4527_implies_Equation4283 (G : Type*) [Magma G] (h : Equation4527 G) : Equation4283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq38 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  have eq215 (X0 X1 X2 X4 : G) : (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) = (X0 ◇ (X1 ◇ X4)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2 in 12
  have eq262 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ sK0) := superpose eq12 eq38 -- superposition 38,12, 12 into 38, unify on (0).2 in 12 and (0).2 in 38
  subsumption eq262 eq215


@[equational_result]
theorem Equation4527_implies_Equation4358 (G : Type*) [Magma G] (h : Equation4527 G) : Equation4358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq38 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  have eq215 (X0 X1 X2 X4 : G) : (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) = (X0 ◇ (X1 ◇ X4)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2 in 12
  have eq262 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ sK0) := superpose eq12 eq38 -- superposition 38,12, 12 into 38, unify on (0).2 in 12 and (0).2 in 38
  subsumption eq262 eq215


@[equational_result]
theorem Equation4527_implies_Equation4432 (G : Type*) [Magma G] (h : Equation4527 G) : Equation4432 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X3) = (X3 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq38 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ X0)) ≠ (sK0 ◇ (sK0 ◇ X1)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq56 (X1 : G) : ((sK1 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ X1)) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1 in 38
  have eq87 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X0) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).2 in 11
  have eq114 (X0 : G) : ((sK1 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ ((X0 ◇ X0) ◇ sK0)) := superpose eq9 eq56 -- superposition 56,9, 9 into 56, unify on (0).2 in 9 and (0).2.2 in 56
  subsumption eq114 eq87


@[equational_result]
theorem Equation4527_implies_Equation4423 (G : Type*) [Magma G] (h : Equation4527 G) : Equation4423 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq226 (X0 X1 X2 X4 : G) : (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) = (X0 ◇ (X1 ◇ X4)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2 in 12
  have eq276 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ sK0) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2 in 18
  subsumption eq276 eq226


@[equational_result]
theorem Equation4527_implies_Equation4284 (G : Type*) [Magma G] (h : Equation4527 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq38 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  have eq215 (X0 X1 X2 X4 : G) : (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) = (X0 ◇ (X1 ◇ X4)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2 in 12
  have eq262 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ sK0) := superpose eq12 eq38 -- superposition 38,12, 12 into 38, unify on (0).2 in 12 and (0).2 in 38
  subsumption eq262 eq215


@[equational_result]
theorem Equation4527_implies_Equation4288 (G : Type*) [Magma G] (h : Equation4527 G) : Equation4288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq38 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  have eq215 (X0 X1 X2 X4 : G) : (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) = (X0 ◇ (X1 ◇ X4)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2 in 12
  have eq262 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ sK0) := superpose eq12 eq38 -- superposition 38,12, 12 into 38, unify on (0).2 in 12 and (0).2 in 38
  subsumption eq262 eq215


@[equational_result]
theorem Equation4527_implies_Equation4318 (G : Type*) [Magma G] (h : Equation4527 G) : Equation4318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq38 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  have eq215 (X0 X1 X2 X4 : G) : (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) = (X0 ◇ (X1 ◇ X4)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2 in 12
  have eq262 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ sK0) := superpose eq12 eq38 -- superposition 38,12, 12 into 38, unify on (0).2 in 12 and (0).2 in 38
  subsumption eq262 eq215


@[equational_result]
theorem Equation4527_implies_Equation4460 (G : Type*) [Magma G] (h : Equation4527 G) : Equation4460 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq226 (X0 X1 X2 X4 : G) : (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) = (X0 ◇ (X1 ◇ X4)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2 in 12
  have eq276 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ sK0) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2 in 18
  subsumption eq276 eq226


@[equational_result]
theorem Equation4527_implies_Equation4286 (G : Type*) [Magma G] (h : Equation4527 G) : Equation4286 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq38 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  have eq215 (X0 X1 X2 X4 : G) : (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) = (X0 ◇ (X1 ◇ X4)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2 in 12
  have eq262 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ sK0) := superpose eq12 eq38 -- superposition 38,12, 12 into 38, unify on (0).2 in 12 and (0).2 in 38
  subsumption eq262 eq215


@[equational_result]
theorem Equation4527_implies_Equation4360 (G : Type*) [Magma G] (h : Equation4527 G) : Equation4360 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq38 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  have eq215 (X0 X1 X2 X4 : G) : (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) = (X0 ◇ (X1 ◇ X4)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2 in 12
  have eq262 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ sK0) := superpose eq12 eq38 -- superposition 38,12, 12 into 38, unify on (0).2 in 12 and (0).2 in 38
  subsumption eq262 eq215


@[equational_result]
theorem Equation4527_implies_Equation4361 (G : Type*) [Magma G] (h : Equation4527 G) : Equation4361 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ sK4)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq38 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  have eq215 (X0 X1 X2 X4 : G) : (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) = (X0 ◇ (X1 ◇ X4)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2 in 12
  have eq262 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ sK0) := superpose eq12 eq38 -- superposition 38,12, 12 into 38, unify on (0).2 in 12 and (0).2 in 38
  subsumption eq262 eq215


@[equational_result]
theorem Equation4527_implies_Equation4506 (G : Type*) [Magma G] (h : Equation4527 G) : Equation4506 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X3) = (X3 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq38 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ X0)) ≠ (sK0 ◇ (sK0 ◇ X1)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq56 (X1 : G) : ((sK1 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ X1)) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1 in 38
  have eq87 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X0) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).2 in 11
  have eq114 (X0 : G) : ((sK1 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ ((X0 ◇ X0) ◇ sK0)) := superpose eq9 eq56 -- superposition 56,9, 9 into 56, unify on (0).2 in 9 and (0).2.2 in 56
  subsumption eq114 eq87


@[equational_result]
theorem Equation4527_implies_Equation4572 (G : Type*) [Magma G] (h : Equation4527 G) : Equation4572 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK3) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq226 (X0 X1 X2 X4 : G) : (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) = (X0 ◇ (X1 ◇ X4)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2 in 12
  have eq276 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ sK0) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2 in 18
  subsumption eq276 eq226


@[equational_result]
theorem Equation4548_implies_Equation4527 (G : Type*) [Magma G] (h : Equation4548 G) : Equation4527 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X3) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq41 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK2)) ≠ (sK0 ◇ (X1 ◇ sK1)) := superpose eq16 eq18 -- superposition 18,16, 16 into 18, unify on (0).2 in 16 and (0).1 in 18
  have eq52 (X1 : G) : ((sK2 ◇ sK2) ◇ sK0) ≠ (sK0 ◇ (X1 ◇ sK1)) := superpose eq9 eq41 -- superposition 41,9, 9 into 41, unify on (0).2 in 9 and (0).1 in 41
  have eq81 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2 in 12
  have eq106 (X0 X1 X2 : G) : ((sK2 ◇ sK2) ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq52 -- superposition 52,12, 12 into 52, unify on (0).2 in 12 and (0).2.2 in 52
  subsumption eq106 eq81


@[equational_result]
theorem Equation4548_implies_Equation4357 (G : Type*) [Magma G] (h : Equation4548 G) : Equation4357 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X3) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq38 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK3)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2 in 12
  have eq89 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK2)) ≠ (sK0 ◇ (X1 ◇ sK3)) := superpose eq16 eq38 -- superposition 38,16, 16 into 38, unify on (0).2 in 16 and (0).1 in 38
  have eq171 (X1 : G) : (sK0 ◇ (X1 ◇ sK3)) ≠ ((sK2 ◇ sK2) ◇ sK0) := superpose eq9 eq89 -- superposition 89,9, 9 into 89, unify on (0).2 in 9 and (0).1 in 89
  have eq403 (X0 X1 X2 : G) : ((sK2 ◇ sK2) ◇ sK0) ≠ (sK0 ◇ (sK3 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq171 -- superposition 171,12, 12 into 171, unify on (0).2 in 12 and (0).1.2 in 171
  subsumption eq403 eq68


@[equational_result]
theorem Equation4548_implies_Equation4622 (G : Type*) [Magma G] (h : Equation4548 G) : Equation4622 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X3) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ (sK1 ◇ (X0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq19 (X0 X1 : G) : (sK1 ◇ (X0 ◇ sK0)) ≠ (sK1 ◇ (X1 ◇ sK2)) := superpose eq9 eq18 -- superposition 18,9, 9 into 18, unify on (0).2 in 9 and (0).1 in 18
  have eq55 (X1 : G) : ((sK2 ◇ sK2) ◇ sK1) ≠ (sK1 ◇ (X1 ◇ sK0)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq80 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2 in 12
  have eq105 (X0 X1 X2 : G) : ((sK2 ◇ sK2) ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq55 -- superposition 55,12, 12 into 55, unify on (0).2 in 12 and (0).2.2 in 55
  subsumption eq105 eq80


@[equational_result]
theorem Equation4548_implies_Equation4314 (G : Type*) [Magma G] (h : Equation4548 G) : Equation4314 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X3) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq38 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2 in 12
  have eq89 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK0)) ≠ (sK0 ◇ (X1 ◇ sK1)) := superpose eq16 eq38 -- superposition 38,16, 16 into 38, unify on (0).2 in 16 and (0).1 in 38
  have eq171 (X1 : G) : (sK0 ◇ (X1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq9 eq89 -- superposition 89,9, 9 into 89, unify on (0).2 in 9 and (0).1 in 89
  have eq403 (X0 X1 X2 : G) : ((sK0 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq171 -- superposition 171,12, 12 into 171, unify on (0).2 in 12 and (0).1.2 in 171
  subsumption eq403 eq68


@[equational_result]
theorem Equation4548_implies_Equation4282 (G : Type*) [Magma G] (h : Equation4548 G) : Equation4282 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X3) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq34 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ X0) = (X0 ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2 in 12
  have eq89 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK1)) ≠ (sK0 ◇ (X1 ◇ sK2)) := superpose eq16 eq34 -- superposition 34,16, 16 into 34, unify on (0).2 in 16 and (0).1 in 34
  have eq171 (X1 : G) : (sK0 ◇ (X1 ◇ sK2)) ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq9 eq89 -- superposition 89,9, 9 into 89, unify on (0).2 in 9 and (0).1 in 89
  have eq403 (X0 X1 X2 : G) : ((sK1 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ (sK2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq171 -- superposition 171,12, 12 into 171, unify on (0).2 in 12 and (0).1.2 in 171
  subsumption eq403 eq68


@[equational_result]
theorem Equation3697_implies_Equation3683 (G : Type*) [Magma G] (h : Equation3697 G) : Equation3683 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = ((X4 ◇ X5) ◇ (X0 ◇ X6)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq31 (X0 X2 X4 X5 : G) : (X0 ◇ X0) = ((X4 ◇ X5) ◇ (X2 ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq108 (X2 X3 X4 X5 X6 : G) : ((X4 ◇ X5) ◇ (X2 ◇ X6)) = (X3 ◇ X3) := superpose eq31 eq11 -- superposition 11,31, 31 into 11, unify on (0).2 in 31 and (0).1 in 11
  have eq137 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (sK2 ◇ X2)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq137 eq108


@[equational_result]
theorem Equation3697_implies_Equation3680 (G : Type*) [Magma G] (h : Equation3697 G) : Equation3680 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = ((X4 ◇ X5) ◇ (X0 ◇ X6)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq31 (X0 X2 X4 X5 : G) : (X0 ◇ X0) = ((X4 ◇ X5) ◇ (X2 ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq108 (X2 X3 X4 X5 X6 : G) : ((X4 ◇ X5) ◇ (X2 ◇ X6)) = (X3 ◇ X3) := superpose eq31 eq11 -- superposition 11,31, 31 into 11, unify on (0).2 in 31 and (0).1 in 11
  have eq137 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (sK2 ◇ X2)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq137 eq108


@[equational_result]
theorem Equation3697_implies_Equation3701 (G : Type*) [Magma G] (h : Equation3697 G) : Equation3701 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = ((X4 ◇ X5) ◇ (X0 ◇ X6)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq31 (X0 X2 X4 X5 : G) : (X0 ◇ X0) = ((X4 ◇ X5) ◇ (X2 ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq108 (X2 X3 X4 X5 X6 : G) : ((X4 ◇ X5) ◇ (X2 ◇ X6)) = (X3 ◇ X3) := superpose eq31 eq11 -- superposition 11,31, 31 into 11, unify on (0).2 in 31 and (0).1 in 11
  have eq137 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (sK1 ◇ X2)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq137 eq108


@[equational_result]
theorem Equation3697_implies_Equation3673 (G : Type*) [Magma G] (h : Equation3697 G) : Equation3673 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = ((X4 ◇ X5) ◇ (X0 ◇ X6)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq31 (X0 X2 X4 X5 : G) : (X0 ◇ X0) = ((X4 ◇ X5) ◇ (X2 ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq108 (X2 X3 X4 X5 X6 : G) : ((X4 ◇ X5) ◇ (X2 ◇ X6)) = (X3 ◇ X3) := superpose eq31 eq11 -- superposition 11,31, 31 into 11, unify on (0).2 in 31 and (0).1 in 11
  have eq137 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (sK2 ◇ X2)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq137 eq108


@[equational_result]
theorem Equation3697_implies_Equation3703 (G : Type*) [Magma G] (h : Equation3697 G) : Equation3703 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = ((X4 ◇ X5) ◇ (X0 ◇ X6)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq31 (X0 X2 X4 X5 : G) : (X0 ◇ X0) = ((X4 ◇ X5) ◇ (X2 ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq108 (X2 X3 X4 X5 X6 : G) : ((X4 ◇ X5) ◇ (X2 ◇ X6)) = (X3 ◇ X3) := superpose eq31 eq11 -- superposition 11,31, 31 into 11, unify on (0).2 in 31 and (0).1 in 11
  have eq137 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (sK2 ◇ X2)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq137 eq108


@[equational_result]
theorem Equation3697_implies_Equation3671 (G : Type*) [Magma G] (h : Equation3697 G) : Equation3671 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = ((X4 ◇ X5) ◇ (X0 ◇ X6)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq31 (X0 X2 X4 X5 : G) : (X0 ◇ X0) = ((X4 ◇ X5) ◇ (X2 ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq108 (X2 X3 X4 X5 X6 : G) : ((X4 ◇ X5) ◇ (X2 ◇ X6)) = (X3 ◇ X3) := superpose eq31 eq11 -- superposition 11,31, 31 into 11, unify on (0).2 in 31 and (0).1 in 11
  have eq137 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (sK2 ◇ X2)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq137 eq108


@[equational_result]
theorem Equation3697_implies_Equation3706 (G : Type*) [Magma G] (h : Equation3697 G) : Equation3706 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = ((X4 ◇ X5) ◇ (X0 ◇ X6)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq31 (X0 X2 X4 X5 : G) : (X0 ◇ X0) = ((X4 ◇ X5) ◇ (X2 ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq108 (X2 X3 X4 X5 X6 : G) : ((X4 ◇ X5) ◇ (X2 ◇ X6)) = (X3 ◇ X3) := superpose eq31 eq11 -- superposition 11,31, 31 into 11, unify on (0).2 in 31 and (0).1 in 11
  have eq137 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (sK3 ◇ X2)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq137 eq108


@[equational_result]
theorem Equation3697_implies_Equation3708 (G : Type*) [Magma G] (h : Equation3697 G) : Equation3708 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = ((X4 ◇ X5) ◇ (X0 ◇ X6)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq31 (X0 X2 X4 X5 : G) : (X0 ◇ X0) = ((X4 ◇ X5) ◇ (X2 ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq108 (X2 X3 X4 X5 X6 : G) : ((X4 ◇ X5) ◇ (X2 ◇ X6)) = (X3 ◇ X3) := superpose eq31 eq11 -- superposition 11,31, 31 into 11, unify on (0).2 in 31 and (0).1 in 11
  have eq137 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (sK3 ◇ X2)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq137 eq108


@[equational_result]
theorem Equation3697_implies_Equation3705 (G : Type*) [Magma G] (h : Equation3697 G) : Equation3705 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = ((X4 ◇ X5) ◇ (X0 ◇ X6)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq31 (X0 X2 X4 X5 : G) : (X0 ◇ X0) = ((X4 ◇ X5) ◇ (X2 ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq108 (X2 X3 X4 X5 X6 : G) : ((X4 ◇ X5) ◇ (X2 ◇ X6)) = (X3 ◇ X3) := superpose eq31 eq11 -- superposition 11,31, 31 into 11, unify on (0).2 in 31 and (0).1 in 11
  have eq137 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (sK2 ◇ X2)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq137 eq108


@[equational_result]
theorem Equation3697_implies_Equation3707 (G : Type*) [Magma G] (h : Equation3697 G) : Equation3707 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = ((X4 ◇ X5) ◇ (X0 ◇ X6)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq31 (X0 X2 X4 X5 : G) : (X0 ◇ X0) = ((X4 ◇ X5) ◇ (X2 ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq108 (X2 X3 X4 X5 X6 : G) : ((X4 ◇ X5) ◇ (X2 ◇ X6)) = (X3 ◇ X3) := superpose eq31 eq11 -- superposition 11,31, 31 into 11, unify on (0).2 in 31 and (0).1 in 11
  have eq137 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (sK3 ◇ X2)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq137 eq108


@[equational_result]
theorem Equation3697_implies_Equation3710 (G : Type*) [Magma G] (h : Equation3697 G) : Equation3710 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK4)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = ((X4 ◇ X5) ◇ (X0 ◇ X6)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq31 (X0 X2 X4 X5 : G) : (X0 ◇ X0) = ((X4 ◇ X5) ◇ (X2 ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq108 (X2 X3 X4 X5 X6 : G) : ((X4 ◇ X5) ◇ (X2 ◇ X6)) = (X3 ◇ X3) := superpose eq31 eq11 -- superposition 11,31, 31 into 11, unify on (0).2 in 31 and (0).1 in 11
  have eq137 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (sK3 ◇ X2)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq137 eq108


@[equational_result]
theorem Equation3683_implies_Equation3697 (G : Type*) [Magma G] (h : Equation3683 G) : Equation3697 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X3)) = ((X4 ◇ X0) ◇ (X5 ◇ X6)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq29 (X1 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ (X4 ◇ X5)) = (X3 ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq109 (X0 X3 X4 X5 X6 : G) : ((X4 ◇ X0) ◇ (X5 ◇ X6)) = (X3 ◇ X3) := superpose eq29 eq11 -- superposition 11,29, 29 into 11, unify on (0).2 in 29 and (0).1 in 11
  have eq137 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ sK2) ◇ (X1 ◇ X2)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq137 eq109


@[equational_result]
theorem Equation3683_implies_Equation3698 (G : Type*) [Magma G] (h : Equation3683 G) : Equation3698 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X3)) = ((X4 ◇ X0) ◇ (X5 ◇ X6)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq29 (X1 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ (X4 ◇ X5)) = (X3 ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq109 (X0 X3 X4 X5 X6 : G) : ((X4 ◇ X0) ◇ (X5 ◇ X6)) = (X3 ◇ X3) := superpose eq29 eq11 -- superposition 11,29, 29 into 11, unify on (0).2 in 29 and (0).1 in 11
  have eq137 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ sK2) ◇ (X1 ◇ X2)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq137 eq109


@[equational_result]
theorem Equation4411_implies_Equation4419 (G : Type*) [Magma G] (h : Equation4411 G) : Equation4419 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X0 ◇ X4) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq33 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ X0) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  have eq138 (X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (((X1 ◇ X2) ◇ sK2) ◇ sK0) := superpose eq17 eq33 -- superposition 33,17, 17 into 33, unify on (0).2 in 17 and (0).2 in 33
  subsumption eq138 eq68


@[equational_result]
theorem Equation4411_implies_Equation4282 (G : Type*) [Magma G] (h : Equation4411 G) : Equation4282 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq62 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  have eq287 (X3 X4 X5 : G) : (X3 ◇ (X3 ◇ X4)) = (X3 ◇ (X3 ◇ X5)) := superpose eq62 eq62 -- superposition 62,62, 62 into 62, unify on (0).2 in 62 and (0).2 in 62
  have eq508 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq287 eq10 -- superposition 10,287, 287 into 10, unify on (0).2 in 287 and (0).2 in 10
  subsumption eq508 eq287


@[equational_result]
theorem Equation4411_implies_Equation4622 (G : Type*) [Magma G] (h : Equation4411 G) : Equation4622 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 : ((sK0 ◇ sK0) ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK2)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 : (sK1 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq64 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).2 in 16
  have eq289 (X3 X4 X5 : G) : (X3 ◇ (X3 ◇ X4)) = (X3 ◇ (X3 ◇ X5)) := superpose eq64 eq64 -- superposition 64,64, 64 into 64, unify on (0).2 in 64 and (0).2 in 64
  have eq510 (X0 : G) : (sK1 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ X0)) := superpose eq289 eq12 -- superposition 12,289, 289 into 12, unify on (0).2 in 289 and (0).1 in 12
  subsumption eq510 eq289


@[equational_result]
theorem Equation4411_implies_Equation4388 (G : Type*) [Magma G] (h : Equation4411 G) : Equation4388 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X0 ◇ X4) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq33 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ X0) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  have eq138 (X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (((X1 ◇ X2) ◇ sK1) ◇ sK0) := superpose eq17 eq33 -- superposition 33,17, 17 into 33, unify on (0).2 in 17 and (0).2 in 33
  subsumption eq138 eq68


@[equational_result]
theorem Equation4411_implies_Equation4415 (G : Type*) [Magma G] (h : Equation4411 G) : Equation4415 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X0 ◇ X4) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq37 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ X0) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  have eq151 (X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (((X1 ◇ X2) ◇ sK2) ◇ sK0) := superpose eq17 eq37 -- superposition 37,17, 17 into 37, unify on (0).2 in 17 and (0).2 in 37
  subsumption eq151 eq68


@[equational_result]
theorem Equation4411_implies_Equation4611 (G : Type*) [Magma G] (h : Equation4411 G) : Equation4611 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 : ((sK0 ◇ sK0) ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq64 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).2 in 16
  have eq289 (X3 X4 X5 : G) : (X3 ◇ (X3 ◇ X4)) = (X3 ◇ (X3 ◇ X5)) := superpose eq64 eq64 -- superposition 64,64, 64 into 64, unify on (0).2 in 64 and (0).2 in 64
  have eq510 (X0 : G) : (sK1 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ X0)) := superpose eq289 eq12 -- superposition 12,289, 289 into 12, unify on (0).2 in 289 and (0).1 in 12
  subsumption eq510 eq289


@[equational_result]
theorem Equation4411_implies_Equation4619 (G : Type*) [Magma G] (h : Equation4411 G) : Equation4619 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 : ((sK0 ◇ sK0) ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK2)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 : (sK1 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq64 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).2 in 16
  have eq289 (X3 X4 X5 : G) : (X3 ◇ (X3 ◇ X4)) = (X3 ◇ (X3 ◇ X5)) := superpose eq64 eq64 -- superposition 64,64, 64 into 64, unify on (0).2 in 64 and (0).2 in 64
  have eq510 (X0 : G) : (sK1 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ X0)) := superpose eq289 eq12 -- superposition 12,289, 289 into 12, unify on (0).2 in 289 and (0).1 in 12
  subsumption eq510 eq289


@[equational_result]
theorem Equation4411_implies_Equation4677 (G : Type*) [Magma G] (h : Equation4411 G) : Equation4677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK1 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 : ((sK0 ◇ sK1) ◇ sK2) ≠ (sK2 ◇ (sK2 ◇ sK1)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 : (sK2 ◇ (sK2 ◇ sK1)) ≠ (sK2 ◇ (sK2 ◇ sK0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq64 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).2 in 16
  have eq289 (X3 X4 X5 : G) : (X3 ◇ (X3 ◇ X4)) = (X3 ◇ (X3 ◇ X5)) := superpose eq64 eq64 -- superposition 64,64, 64 into 64, unify on (0).2 in 64 and (0).2 in 64
  have eq510 (X0 : G) : (sK2 ◇ (sK2 ◇ sK0)) ≠ (sK2 ◇ (sK2 ◇ X0)) := superpose eq289 eq12 -- superposition 12,289, 289 into 12, unify on (0).2 in 289 and (0).1 in 12
  subsumption eq510 eq289


@[equational_result]
theorem Equation4411_implies_Equation4398 (G : Type*) [Magma G] (h : Equation4411 G) : Equation4398 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq63 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2 in 15
  have eq288 (X3 X4 X5 : G) : (X3 ◇ (X3 ◇ X4)) = (X3 ◇ (X3 ◇ X5)) := superpose eq63 eq63 -- superposition 63,63, 63 into 63, unify on (0).2 in 63 and (0).2 in 63
  have eq509 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq288 eq11 -- superposition 11,288, 288 into 11, unify on (0).2 in 288 and (0).1 in 11
  subsumption eq509 eq288


@[equational_result]
theorem Equation4411_implies_Equation4606 (G : Type*) [Magma G] (h : Equation4411 G) : Equation4606 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 : ((sK0 ◇ sK0) ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq64 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).2 in 16
  have eq289 (X3 X4 X5 : G) : (X3 ◇ (X3 ◇ X4)) = (X3 ◇ (X3 ◇ X5)) := superpose eq64 eq64 -- superposition 64,64, 64 into 64, unify on (0).2 in 64 and (0).2 in 64
  have eq510 (X0 : G) : (sK1 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ X0)) := superpose eq289 eq12 -- superposition 12,289, 289 into 12, unify on (0).2 in 289 and (0).1 in 12
  subsumption eq510 eq289


@[equational_result]
theorem Equation4411_implies_Equation4693 (G : Type*) [Magma G] (h : Equation4411 G) : Equation4693 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK3 ◇ sK4) ◇ sK2) := mod_symm nh
  have eq11 : ((sK0 ◇ sK1) ◇ sK2) ≠ (sK2 ◇ (sK2 ◇ sK3)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 : (sK2 ◇ (sK2 ◇ sK3)) ≠ (sK2 ◇ (sK2 ◇ sK0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq64 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).2 in 16
  have eq289 (X3 X4 X5 : G) : (X3 ◇ (X3 ◇ X4)) = (X3 ◇ (X3 ◇ X5)) := superpose eq64 eq64 -- superposition 64,64, 64 into 64, unify on (0).2 in 64 and (0).2 in 64
  have eq510 (X0 : G) : (sK2 ◇ (sK2 ◇ sK0)) ≠ (sK2 ◇ (sK2 ◇ X0)) := superpose eq289 eq12 -- superposition 12,289, 289 into 12, unify on (0).2 in 289 and (0).1 in 12
  subsumption eq510 eq289


@[equational_result]
theorem Equation4411_implies_Equation4423 (G : Type*) [Magma G] (h : Equation4411 G) : Equation4423 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X0 ◇ X4) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq33 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ X0) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  have eq138 (X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (((X1 ◇ X2) ◇ sK2) ◇ sK0) := superpose eq17 eq33 -- superposition 33,17, 17 into 33, unify on (0).2 in 17 and (0).2 in 33
  subsumption eq138 eq68


@[equational_result]
theorem Equation4411_implies_Equation4401 (G : Type*) [Magma G] (h : Equation4411 G) : Equation4401 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq63 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2 in 15
  have eq288 (X3 X4 X5 : G) : (X3 ◇ (X3 ◇ X4)) = (X3 ◇ (X3 ◇ X5)) := superpose eq63 eq63 -- superposition 63,63, 63 into 63, unify on (0).2 in 63 and (0).2 in 63
  have eq509 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq288 eq11 -- superposition 11,288, 288 into 11, unify on (0).2 in 288 and (0).1 in 11
  subsumption eq509 eq288


@[equational_result]
theorem Equation4411_implies_Equation4427 (G : Type*) [Magma G] (h : Equation4411 G) : Equation4427 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X0 ◇ X4) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq33 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ X0) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  have eq138 (X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (((X1 ◇ X2) ◇ sK2) ◇ sK0) := superpose eq17 eq33 -- superposition 33,17, 17 into 33, unify on (0).2 in 17 and (0).2 in 33
  subsumption eq138 eq68


@[equational_result]
theorem Equation4419_implies_Equation4411 (G : Type*) [Magma G] (h : Equation4419 G) : Equation4411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X0) = ((X3 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (((X2 ◇ X1) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X2)) = ((X2 ◇ (X2 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq20 (X1 X2 X3 X4 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ X3) = ((X4 ◇ X2) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq33 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X0 ◇ sK2) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq69 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq187 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq20 eq11 -- superposition 11,20, 20 into 11, unify on (0).2 in 20 and (0).2.2 in 11
  have eq188 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).2.2 in 11
  have eq395 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  have eq430 (X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ (sK2 ◇ X1))) := superpose eq14 eq33 -- superposition 33,14, 14 into 33, unify on (0).2 in 14 and (0).2 in 33
  have eq458 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq9 eq395 -- forward demodulation 395,9
  have eq459 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ X1)) := superpose eq69 eq458 -- forward demodulation 458,69
  have eq460 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = ((X3 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq459 eq188 -- backward demodulation 188,459
  have eq463 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq460 eq187 -- backward demodulation 187,460
  have eq466 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq463 eq11 -- backward demodulation 11,463
  have eq564 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose eq15 eq466 -- superposition 466,15, 15 into 466, unify on (0).2 in 15 and (0).2 in 466
  have eq600 (X1 : G) : (sK0 ◇ (sK0 ◇ (sK2 ◇ X1))) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq564 eq430 -- backward demodulation 430,564
  subsumption eq600 eq564


@[equational_result]
theorem Equation4419_implies_Equation4405 (G : Type*) [Magma G] (h : Equation4419 G) : Equation4405 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X0) = ((X3 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (((X2 ◇ X1) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X2)) = ((X2 ◇ (X2 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq20 (X1 X2 X3 X4 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ X3) = ((X4 ◇ X2) ◇ X3) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1.1 in 14
  have eq61 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq175 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq20 eq12 -- superposition 12,20, 20 into 12, unify on (0).2 in 20 and (0).2.2 in 12
  have eq176 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2.2 in 12
  have eq380 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2 in 15
  have eq441 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq9 eq380 -- forward demodulation 380,9
  have eq442 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ X1)) := superpose eq61 eq441 -- forward demodulation 441,61
  have eq443 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = ((X3 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq442 eq176 -- backward demodulation 176,442
  have eq446 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq443 eq175 -- backward demodulation 175,443
  have eq452 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq446 eq12 -- backward demodulation 12,446
  have eq547 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose eq16 eq452 -- superposition 452,16, 16 into 452, unify on (0).2 in 16 and (0).2 in 452
  have eq789 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq547 eq11 -- superposition 11,547, 547 into 11, unify on (0).2 in 547 and (0).1 in 11
  subsumption eq789 rfl


@[equational_result]
theorem Equation4419_implies_Equation4599 (G : Type*) [Magma G] (h : Equation4419 G) : Equation4599 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 : ((sK0 ◇ sK0) ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X0) = ((X3 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (((X2 ◇ X1) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X2)) = ((X2 ◇ (X2 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq21 (X1 X2 X3 X4 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ X3) = ((X4 ◇ X2) ◇ X3) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).1.1 in 15
  have eq62 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq176 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq21 eq13 -- superposition 13,21, 21 into 13, unify on (0).2 in 21 and (0).2.2 in 13
  have eq177 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq17 eq13 -- superposition 13,17, 17 into 13, unify on (0).2 in 17 and (0).2.2 in 13
  have eq381 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) := superpose eq17 eq16 -- superposition 16,17, 17 into 16, unify on (0).2 in 17 and (0).2 in 16
  have eq442 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq9 eq381 -- forward demodulation 381,9
  have eq443 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ X1)) := superpose eq62 eq442 -- forward demodulation 442,62
  have eq444 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = ((X3 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq443 eq177 -- backward demodulation 177,443
  have eq447 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq444 eq176 -- backward demodulation 176,444
  have eq453 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq447 eq13 -- backward demodulation 13,447
  have eq548 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose eq17 eq453 -- superposition 453,17, 17 into 453, unify on (0).2 in 17 and (0).2 in 453
  have eq785 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := superpose eq548 eq548 -- superposition 548,548, 548 into 548, unify on (0).2 in 548 and (0).2 in 548
  have eq820 (X0 : G) : (sK1 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ X0)) := superpose eq548 eq12 -- superposition 12,548, 548 into 12, unify on (0).2 in 548 and (0).1 in 12
  subsumption eq820 eq785


@[equational_result]
theorem Equation4419_implies_Equation4631 (G : Type*) [Magma G] (h : Equation4419 G) : Equation4631 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK2)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 : (sK0 ◇ (sK0 ◇ sK2)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X0) = ((X3 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (((X2 ◇ X1) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X2)) = ((X2 ◇ (X2 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq21 (X1 X2 X3 X4 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ X3) = ((X4 ◇ X2) ◇ X3) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).1.1 in 15
  have eq62 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq176 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq21 eq13 -- superposition 13,21, 21 into 13, unify on (0).2 in 21 and (0).2.2 in 13
  have eq177 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq17 eq13 -- superposition 13,17, 17 into 13, unify on (0).2 in 17 and (0).2.2 in 13
  have eq381 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) := superpose eq17 eq16 -- superposition 16,17, 17 into 16, unify on (0).2 in 17 and (0).2 in 16
  have eq442 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq9 eq381 -- forward demodulation 381,9
  have eq443 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ X1)) := superpose eq62 eq442 -- forward demodulation 442,62
  have eq444 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = ((X3 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq443 eq177 -- backward demodulation 177,443
  have eq447 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq444 eq176 -- backward demodulation 176,444
  have eq453 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq447 eq13 -- backward demodulation 13,447
  have eq548 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose eq17 eq453 -- superposition 453,17, 17 into 453, unify on (0).2 in 17 and (0).2 in 453
  have eq583 : (sK0 ◇ (sK0 ◇ sK2)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq548 eq12 -- backward demodulation 12,548
  subsumption eq583 eq548


@[equational_result]
theorem Equation4419_implies_Equation4391 (G : Type*) [Magma G] (h : Equation4419 G) : Equation4391 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X0) = ((X3 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (((X2 ◇ X1) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X2)) = ((X2 ◇ (X2 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 X2 X3 X4 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ X3) = ((X4 ◇ X2) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq69 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq187 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq20 eq11 -- superposition 11,20, 20 into 11, unify on (0).2 in 20 and (0).2.2 in 11
  have eq188 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).2.2 in 11
  have eq395 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  have eq458 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq9 eq395 -- forward demodulation 395,9
  have eq459 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ X1)) := superpose eq69 eq458 -- forward demodulation 458,69
  have eq460 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = ((X3 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq459 eq188 -- backward demodulation 188,459
  have eq463 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq460 eq187 -- backward demodulation 187,460
  have eq466 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq463 eq11 -- backward demodulation 11,463
  have eq564 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose eq15 eq466 -- superposition 466,15, 15 into 466, unify on (0).2 in 15 and (0).2 in 466
  have eq837 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq564 eq16 -- superposition 16,564, 564 into 16, unify on (0).2 in 564 and (0).2 in 16
  subsumption eq837 rfl


@[equational_result]
theorem Equation4419_implies_Equation4382 (G : Type*) [Magma G] (h : Equation4419 G) : Equation4382 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X0) = ((X3 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (((X2 ◇ X1) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X2)) = ((X2 ◇ (X2 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 X2 X3 X4 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ X3) = ((X4 ◇ X2) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq69 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq187 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq20 eq11 -- superposition 11,20, 20 into 11, unify on (0).2 in 20 and (0).2.2 in 11
  have eq188 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).2.2 in 11
  have eq395 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  have eq458 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq9 eq395 -- forward demodulation 395,9
  have eq459 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ X1)) := superpose eq69 eq458 -- forward demodulation 458,69
  have eq460 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = ((X3 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq459 eq188 -- backward demodulation 188,459
  have eq463 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq460 eq187 -- backward demodulation 187,460
  have eq466 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq463 eq11 -- backward demodulation 11,463
  have eq564 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose eq15 eq466 -- superposition 466,15, 15 into 466, unify on (0).2 in 15 and (0).2 in 466
  have eq807 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq564 eq16 -- superposition 16,564, 564 into 16, unify on (0).2 in 564 and (0).2 in 16
  subsumption eq807 rfl


@[equational_result]
theorem Equation4419_implies_Equation4395 (G : Type*) [Magma G] (h : Equation4419 G) : Equation4395 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X0) = ((X3 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (((X2 ◇ X1) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X2)) = ((X2 ◇ (X2 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq20 (X1 X2 X3 X4 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ X3) = ((X4 ◇ X2) ◇ X3) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1.1 in 14
  have eq61 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq175 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq20 eq12 -- superposition 12,20, 20 into 12, unify on (0).2 in 20 and (0).2.2 in 12
  have eq176 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2.2 in 12
  have eq380 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2 in 15
  have eq441 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq9 eq380 -- forward demodulation 380,9
  have eq442 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ X1)) := superpose eq61 eq441 -- forward demodulation 441,61
  have eq443 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = ((X3 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq442 eq176 -- backward demodulation 176,442
  have eq446 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq443 eq175 -- backward demodulation 175,443
  have eq452 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq446 eq12 -- backward demodulation 12,446
  have eq547 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose eq16 eq452 -- superposition 452,16, 16 into 452, unify on (0).2 in 16 and (0).2 in 452
  have eq789 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq547 eq11 -- superposition 11,547, 547 into 11, unify on (0).2 in 547 and (0).1 in 11
  subsumption eq789 rfl


@[equational_result]
theorem Equation4419_implies_Equation4675 (G : Type*) [Magma G] (h : Equation4419 G) : Equation4675 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq11 : ((sK0 ◇ sK1) ◇ sK2) ≠ (sK2 ◇ (sK2 ◇ sK3)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 : (sK2 ◇ (sK2 ◇ sK3)) ≠ (sK2 ◇ (sK2 ◇ sK1)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X0) = ((X3 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (((X2 ◇ X1) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X2)) = ((X2 ◇ (X2 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq21 (X1 X2 X3 X4 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ X3) = ((X4 ◇ X2) ◇ X3) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).1.1 in 15
  have eq62 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq176 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq21 eq13 -- superposition 13,21, 21 into 13, unify on (0).2 in 21 and (0).2.2 in 13
  have eq177 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq17 eq13 -- superposition 13,17, 17 into 13, unify on (0).2 in 17 and (0).2.2 in 13
  have eq381 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) := superpose eq17 eq16 -- superposition 16,17, 17 into 16, unify on (0).2 in 17 and (0).2 in 16
  have eq442 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq9 eq381 -- forward demodulation 381,9
  have eq443 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X3 ◇ X1)) := superpose eq62 eq442 -- forward demodulation 442,62
  have eq444 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = ((X3 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq443 eq177 -- backward demodulation 177,443
  have eq447 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq444 eq176 -- backward demodulation 176,444
  have eq453 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq447 eq13 -- backward demodulation 13,447
  have eq548 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose eq17 eq453 -- superposition 453,17, 17 into 453, unify on (0).2 in 17 and (0).2 in 453
  have eq785 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := superpose eq548 eq548 -- superposition 548,548, 548 into 548, unify on (0).2 in 548 and (0).2 in 548
  have eq790 : (sK2 ◇ (sK2 ◇ sK1)) ≠ (sK2 ◇ (sK2 ◇ sK2)) := superpose eq548 eq12 -- superposition 12,548, 548 into 12, unify on (0).2 in 548 and (0).1 in 12
  subsumption eq790 eq785


@[equational_result]
theorem Equation4567_implies_Equation4445 (G : Type*) [Magma G] (h : Equation4567 G) : Equation4445 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 X3 X4 X5 : G) : ((X5 ◇ X2) ◇ X4) = (X4 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ X2)) = ((X2 ◇ (X3 ◇ X1)) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X1)) = (X2 ◇ (X4 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq82 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq210 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X5 ◇ X0)) = (X3 ◇ (X4 ◇ (X1 ◇ X2))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq254 (X1 X2 X3 X4 : G) : (sK0 ◇ (sK1 ◇ (X1 ◇ (X2 ◇ X3)))) ≠ (sK0 ◇ (X4 ◇ sK0)) := superpose eq12 eq82 -- superposition 82,12, 12 into 82, unify on (0).2 in 12 and (0).1.2 in 82
  subsumption eq254 eq210


@[equational_result]
theorem Equation4567_implies_Equation4544 (G : Type*) [Magma G] (h : Equation4567 G) : Equation4544 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 X3 X4 X5 : G) : ((X5 ◇ X2) ◇ X4) = (X4 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ X2)) = ((X2 ◇ (X3 ◇ X1)) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X1)) = (X2 ◇ (X4 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq82 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq210 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X5 ◇ X0)) = (X3 ◇ (X4 ◇ (X1 ◇ X2))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq254 (X1 X2 X3 X4 : G) : (sK0 ◇ (sK1 ◇ (X1 ◇ (X2 ◇ X3)))) ≠ (sK0 ◇ (X4 ◇ sK2)) := superpose eq12 eq82 -- superposition 82,12, 12 into 82, unify on (0).2 in 12 and (0).1.2 in 82
  subsumption eq254 eq210


@[equational_result]
theorem Equation4567_implies_Equation4562 (G : Type*) [Magma G] (h : Equation4567 G) : Equation4562 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 X3 X4 X5 : G) : ((X5 ◇ X2) ◇ X4) = (X4 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ X2)) = ((X2 ◇ (X3 ◇ X1)) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X1)) = (X2 ◇ (X4 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq82 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq210 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X5 ◇ X0)) = (X3 ◇ (X4 ◇ (X1 ◇ X2))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq254 (X1 X2 X3 X4 : G) : (sK0 ◇ (sK1 ◇ (X1 ◇ (X2 ◇ X3)))) ≠ (sK0 ◇ (X4 ◇ sK2)) := superpose eq12 eq82 -- superposition 82,12, 12 into 82, unify on (0).2 in 12 and (0).1.2 in 82
  subsumption eq254 eq210


@[equational_result]
theorem Equation4552_implies_Equation4567 (G : Type*) [Magma G] (h : Equation4552 G) : Equation4567 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 X3 X4 X5 : G) : ((X2 ◇ X5) ◇ X4) = (X4 ◇ (X2 ◇ (X3 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ X0)) = (((X2 ◇ X3) ◇ X0) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X0)) = (X2 ◇ (X4 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK3)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq82 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK3)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq210 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X5 ◇ X2)) = (X3 ◇ (X4 ◇ (X0 ◇ X1))) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq254 (X0 X2 X3 X4 : G) : (sK0 ◇ (sK3 ◇ (X0 ◇ (X2 ◇ X3)))) ≠ (sK0 ◇ (X4 ◇ sK2)) := superpose eq12 eq82 -- superposition 82,12, 12 into 82, unify on (0).2 in 12 and (0).1.2 in 82
  subsumption eq254 eq210


@[equational_result]
theorem Equation4552_implies_Equation4472 (G : Type*) [Magma G] (h : Equation4552 G) : Equation4472 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 X3 X4 X5 : G) : ((X2 ◇ X5) ◇ X4) = (X4 ◇ (X2 ◇ (X3 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ X0)) = (((X2 ◇ X3) ◇ X0) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X0)) = (X2 ◇ (X4 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq82 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq210 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X5 ◇ X2)) = (X3 ◇ (X4 ◇ (X0 ◇ X1))) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq254 (X0 X2 X3 X4 : G) : (sK0 ◇ (sK0 ◇ (X0 ◇ (X2 ◇ X3)))) ≠ (sK0 ◇ (X4 ◇ sK1)) := superpose eq12 eq82 -- superposition 82,12, 12 into 82, unify on (0).2 in 12 and (0).1.2 in 82
  subsumption eq254 eq210


@[equational_result]
theorem Equation4552_implies_Equation4557 (G : Type*) [Magma G] (h : Equation4552 G) : Equation4557 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 X3 X4 X5 : G) : ((X2 ◇ X5) ◇ X4) = (X4 ◇ (X2 ◇ (X3 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ X0)) = (((X2 ◇ X3) ◇ X0) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X0)) = (X2 ◇ (X4 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK3)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq75 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK3)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq210 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X5 ◇ X2)) = (X3 ◇ (X4 ◇ (X0 ◇ X1))) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq254 (X0 X2 X3 X4 : G) : (sK0 ◇ (sK3 ◇ (X0 ◇ (X2 ◇ X3)))) ≠ (sK0 ◇ (X4 ◇ sK2)) := superpose eq12 eq75 -- superposition 75,12, 12 into 75, unify on (0).2 in 12 and (0).1.2 in 75
  subsumption eq254 eq210


@[equational_result]
theorem Equation4552_implies_Equation4448 (G : Type*) [Magma G] (h : Equation4552 G) : Equation4448 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 X3 X4 X5 : G) : ((X2 ◇ X5) ◇ X4) = (X4 ◇ (X2 ◇ (X3 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ X0)) = (((X2 ◇ X3) ◇ X0) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X0)) = (X2 ◇ (X4 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq82 (X0 X1 : G) : (sK0 ◇ (X1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq210 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X5 ◇ X2)) = (X3 ◇ (X4 ◇ (X0 ◇ X1))) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq254 (X0 X2 X3 X4 : G) : (sK0 ◇ (sK1 ◇ (X0 ◇ (X2 ◇ X3)))) ≠ (sK0 ◇ (X4 ◇ sK0)) := superpose eq12 eq82 -- superposition 82,12, 12 into 82, unify on (0).2 in 12 and (0).1.2 in 82
  subsumption eq254 eq210


@[equational_result]
theorem Equation4535_implies_Equation4552 (G : Type*) [Magma G] (h : Equation4535 G) : Equation4552 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK3) ◇ sK0) := mod_symm nh
  have eq15 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = (((X1 ◇ X3) ◇ X0) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ X3)) = (X2 ◇ (X0 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ ((X0 ◇ X2) ◇ sK2)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.2 in 19
  have eq208 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X5)) = (X3 ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq268 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2 in 20
  subsumption eq268 eq208


@[equational_result]
theorem Equation4535_implies_Equation4408 (G : Type*) [Magma G] (h : Equation4535 G) : Equation4408 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq15 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = (((X1 ◇ X3) ◇ X0) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ X3)) = (X2 ◇ (X0 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ ((X0 ◇ X2) ◇ sK1)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.2 in 19
  have eq208 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X5)) = (X3 ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq268 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2 in 20
  subsumption eq268 eq208


@[equational_result]
theorem Equation4535_implies_Equation4577 (G : Type*) [Magma G] (h : Equation4535 G) : Equation4577 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK4) ◇ sK0) := mod_symm nh
  have eq15 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = (((X1 ◇ X3) ◇ X0) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ X3)) = (X2 ◇ (X0 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ ((X0 ◇ X2) ◇ sK3)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.2 in 19
  have eq208 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X5)) = (X3 ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq268 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2 in 20
  subsumption eq268 eq208


@[equational_result]
theorem Equation4562_implies_Equation4419 (G : Type*) [Magma G] (h : Equation4562 G) : Equation4419 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq16 (X1 X2 X3 X4 X5 : G) : (X4 ◇ (X2 ◇ X5)) = ((X2 ◇ (X1 ◇ X3)) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X2 ◇ (X1 ◇ X3)) = (X2 ◇ (X1 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ ((X2 ◇ X0) ◇ sK1)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.2 in 19
  have eq208 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X0 ◇ X5)) = (X3 ◇ ((X1 ◇ X2) ◇ X4)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq268 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2 in 20
  subsumption eq268 eq208


@[equational_result]
theorem Equation4562_implies_Equation4485 (G : Type*) [Magma G] (h : Equation4562 G) : Equation4485 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK1 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq16 (X1 X2 X3 X4 X5 : G) : (X4 ◇ (X2 ◇ X5)) = ((X2 ◇ (X1 ◇ X3)) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X2 ◇ (X1 ◇ X3)) = (X2 ◇ (X1 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X2 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ ((X2 ◇ X0) ◇ sK2)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.2 in 19
  have eq208 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X0 ◇ X5)) = (X3 ◇ ((X1 ◇ X2) ◇ X4)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq268 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2 in 20
  subsumption eq268 eq208


@[equational_result]
theorem Equation4562_implies_Equation4548 (G : Type*) [Magma G] (h : Equation4562 G) : Equation4548 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq16 (X1 X2 X3 X4 X5 : G) : (X4 ◇ (X2 ◇ X5)) = ((X2 ◇ (X1 ◇ X3)) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X2 ◇ (X1 ◇ X3)) = (X2 ◇ (X1 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ ((X2 ◇ X0) ◇ sK2)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.2 in 19
  have eq208 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X0 ◇ X5)) = (X3 ◇ ((X1 ◇ X2) ◇ X4)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq268 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2 in 20
  subsumption eq268 eq208


@[equational_result]
theorem Equation4562_implies_Equation4514 (G : Type*) [Magma G] (h : Equation4562 G) : Equation4514 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq16 (X1 X2 X3 X4 X5 : G) : (X4 ◇ (X2 ◇ X5)) = ((X2 ◇ (X1 ◇ X3)) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X2 ◇ (X1 ◇ X3)) = (X2 ◇ (X1 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ ((X2 ◇ X0) ◇ sK2)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.2 in 19
  have eq208 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X0 ◇ X5)) = (X3 ◇ ((X1 ◇ X2) ◇ X4)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq268 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2 in 20
  subsumption eq268 eq208


@[equational_result]
theorem Equation4562_implies_Equation4535 (G : Type*) [Magma G] (h : Equation4562 G) : Equation4535 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK3) ◇ sK0) := mod_symm nh
  have eq16 (X1 X2 X3 X4 X5 : G) : (X4 ◇ (X2 ◇ X5)) = ((X2 ◇ (X1 ◇ X3)) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X2 ◇ (X1 ◇ X3)) = (X2 ◇ (X1 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ ((X2 ◇ X0) ◇ sK3)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.2 in 19
  have eq208 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X0 ◇ X5)) = (X3 ◇ ((X1 ◇ X2) ◇ X4)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq268 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2 in 20
  subsumption eq268 eq208


@[equational_result]
theorem Equation4568_implies_Equation4526 (G : Type*) [Magma G] (h : Equation4568 G) : Equation4526 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK0) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X1 ◇ X2)) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X1)) = (X4 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK3 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq77 (X0 X1 : G) : (X1 ◇ (sK3 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq293 (X1 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ (X3 ◇ X4)) = (X6 ◇ ((X7 ◇ X2) ◇ X1)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1 in 11
  have eq355 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ X2) ◇ X1)) ≠ (X5 ◇ (sK3 ◇ sK0)) := superpose eq11 eq77 -- superposition 77,11, 11 into 77, unify on (0).2 in 11 and (0).2 in 77
  subsumption eq355 eq293


@[equational_result]
theorem Equation4568_implies_Equation4531 (G : Type*) [Magma G] (h : Equation4568 G) : Equation4531 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X1 ◇ X2)) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X1)) = (X4 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq77 (X0 X1 : G) : (X1 ◇ (sK0 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq293 (X1 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ (X3 ◇ X4)) = (X6 ◇ ((X7 ◇ X2) ◇ X1)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1 in 11
  have eq355 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ X2) ◇ X1)) ≠ (X5 ◇ (sK1 ◇ sK2)) := superpose eq11 eq77 -- superposition 77,11, 11 into 77, unify on (0).2 in 11 and (0).1 in 77
  subsumption eq355 eq293


@[equational_result]
theorem Equation4568_implies_Equation4579 (G : Type*) [Magma G] (h : Equation4568 G) : Equation4579 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK4) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X1 ◇ X2)) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X1)) = (X4 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK2 ◇ sK4)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq77 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK4)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq293 (X1 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ (X3 ◇ X4)) = (X6 ◇ ((X7 ◇ X2) ◇ X1)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1 in 11
  have eq355 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ X2) ◇ X1)) ≠ (X5 ◇ (sK2 ◇ sK4)) := superpose eq11 eq77 -- superposition 77,11, 11 into 77, unify on (0).2 in 11 and (0).2 in 77
  subsumption eq355 eq293


@[equational_result]
theorem Equation4568_implies_Equation4567 (G : Type*) [Magma G] (h : Equation4568 G) : Equation4567 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X1 ◇ X2)) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X1)) = (X4 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK0 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq77 (X0 X1 : G) : (X1 ◇ (sK0 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq293 (X1 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ (X3 ◇ X4)) = (X6 ◇ ((X7 ◇ X2) ◇ X1)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1 in 11
  have eq355 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ X2) ◇ X1)) ≠ (X5 ◇ (sK1 ◇ sK2)) := superpose eq11 eq77 -- superposition 77,11, 11 into 77, unify on (0).2 in 11 and (0).1 in 77
  subsumption eq355 eq293


@[equational_result]
theorem Equation4568_implies_Equation4403 (G : Type*) [Magma G] (h : Equation4568 G) : Equation4403 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X1 ◇ X2)) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X1)) = (X4 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq70 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK2)) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq293 (X1 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ (X3 ◇ X4)) = (X6 ◇ ((X7 ◇ X2) ◇ X1)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1 in 11
  have eq355 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ X2) ◇ X1)) ≠ (X5 ◇ (sK2 ◇ sK2)) := superpose eq11 eq70 -- superposition 70,11, 11 into 70, unify on (0).2 in 11 and (0).2 in 70
  subsumption eq355 eq293


@[equational_result]
theorem Equation4568_implies_Equation4542 (G : Type*) [Magma G] (h : Equation4568 G) : Equation4542 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X1 ◇ X2)) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X1)) = (X4 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK2 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq77 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq293 (X1 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ (X3 ◇ X4)) = (X6 ◇ ((X7 ◇ X2) ◇ X1)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1 in 11
  have eq355 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ X2) ◇ X1)) ≠ (X5 ◇ (sK2 ◇ sK0)) := superpose eq11 eq77 -- superposition 77,11, 11 into 77, unify on (0).2 in 11 and (0).2 in 77
  subsumption eq355 eq293


@[equational_result]
theorem Equation4568_implies_Equation4545 (G : Type*) [Magma G] (h : Equation4568 G) : Equation4545 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X1 ◇ X2)) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X1)) = (X4 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq70 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq293 (X1 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ (X3 ◇ X4)) = (X6 ◇ ((X7 ◇ X2) ◇ X1)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1 in 11
  have eq354 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ X2) ◇ X1)) ≠ (X5 ◇ (sK1 ◇ sK2)) := superpose eq11 eq70 -- superposition 70,11, 11 into 70, unify on (0).2 in 11 and (0).1 in 70
  subsumption eq354 eq293


@[equational_result]
theorem Equation4568_implies_Equation4582 (G : Type*) [Magma G] (h : Equation4568 G) : Equation4582 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, sK5, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK4) ◇ sK5) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X1 ◇ X2)) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X1)) = (X4 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK5 ◇ sK4)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq77 (X0 X1 : G) : (X1 ◇ (sK5 ◇ sK4)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq293 (X1 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ (X3 ◇ X4)) = (X6 ◇ ((X7 ◇ X2) ◇ X1)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1 in 11
  have eq355 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ X2) ◇ X1)) ≠ (X5 ◇ (sK5 ◇ sK4)) := superpose eq11 eq77 -- superposition 77,11, 11 into 77, unify on (0).2 in 11 and (0).2 in 77
  subsumption eq355 eq293


@[equational_result]
theorem Equation4568_implies_Equation4400 (G : Type*) [Magma G] (h : Equation4568 G) : Equation4400 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X1 ◇ X2)) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X1)) = (X4 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq77 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK1)) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq293 (X1 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ (X3 ◇ X4)) = (X6 ◇ ((X7 ◇ X2) ◇ X1)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1 in 11
  have eq355 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ X2) ◇ X1)) ≠ (X5 ◇ (sK2 ◇ sK1)) := superpose eq11 eq77 -- superposition 77,11, 11 into 77, unify on (0).2 in 11 and (0).2 in 77
  subsumption eq355 eq293


@[equational_result]
theorem Equation4568_implies_Equation4524 (G : Type*) [Magma G] (h : Equation4568 G) : Equation4524 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X1 ◇ X2)) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X1)) = (X4 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq77 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq293 (X1 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ (X3 ◇ X4)) = (X6 ◇ ((X7 ◇ X2) ◇ X1)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1 in 11
  have eq354 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ X2) ◇ X1)) ≠ (X5 ◇ (sK1 ◇ sK2)) := superpose eq11 eq77 -- superposition 77,11, 11 into 77, unify on (0).2 in 11 and (0).1 in 77
  subsumption eq354 eq293


@[equational_result]
theorem Equation4568_implies_Equation4481 (G : Type*) [Magma G] (h : Equation4568 G) : Equation4481 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK1 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X1 ◇ X2)) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X1)) = (X4 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq77 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq293 (X1 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ (X3 ◇ X4)) = (X6 ◇ ((X7 ◇ X2) ◇ X1)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1 in 11
  have eq355 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ X2) ◇ X1)) ≠ (X5 ◇ (sK2 ◇ sK0)) := superpose eq11 eq77 -- superposition 77,11, 11 into 77, unify on (0).2 in 11 and (0).2 in 77
  subsumption eq355 eq293


@[equational_result]
theorem Equation4568_implies_Equation4564 (G : Type*) [Magma G] (h : Equation4568 G) : Equation4564 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X1 ◇ X2)) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X1)) = (X4 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK2 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq77 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq293 (X1 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ (X3 ◇ X4)) = (X6 ◇ ((X7 ◇ X2) ◇ X1)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1 in 11
  have eq355 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ X2) ◇ X1)) ≠ (X5 ◇ (sK2 ◇ sK1)) := superpose eq11 eq77 -- superposition 77,11, 11 into 77, unify on (0).2 in 11 and (0).2 in 77
  subsumption eq355 eq293


@[equational_result]
theorem Equation4568_implies_Equation4541 (G : Type*) [Magma G] (h : Equation4568 G) : Equation4541 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X1 ◇ X2)) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X1)) = (X4 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq77 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq293 (X1 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ (X3 ◇ X4)) = (X6 ◇ ((X7 ◇ X2) ◇ X1)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1 in 11
  have eq354 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ X2) ◇ X1)) ≠ (X5 ◇ (sK1 ◇ sK2)) := superpose eq11 eq77 -- superposition 77,11, 11 into 77, unify on (0).2 in 11 and (0).1 in 77
  subsumption eq354 eq293


@[equational_result]
theorem Equation4568_implies_Equation4444 (G : Type*) [Magma G] (h : Equation4568 G) : Equation4444 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X1 ◇ X2)) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X1)) = (X4 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq77 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK0)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq293 (X1 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ (X3 ◇ X4)) = (X6 ◇ ((X7 ◇ X2) ◇ X1)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1 in 11
  have eq355 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ X2) ◇ X1)) ≠ (X5 ◇ (sK2 ◇ sK0)) := superpose eq11 eq77 -- superposition 77,11, 11 into 77, unify on (0).2 in 11 and (0).2 in 77
  subsumption eq355 eq293


@[equational_result]
theorem Equation4568_implies_Equation4396 (G : Type*) [Magma G] (h : Equation4568 G) : Equation4396 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X1 ◇ X2)) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X1)) = (X4 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq77 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq293 (X1 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ (X3 ◇ X4)) = (X6 ◇ ((X7 ◇ X2) ◇ X1)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1 in 11
  have eq355 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ X2) ◇ X1)) ≠ (X5 ◇ (sK1 ◇ sK0)) := superpose eq11 eq77 -- superposition 77,11, 11 into 77, unify on (0).2 in 11 and (0).2 in 77
  subsumption eq355 eq293


@[equational_result]
theorem Equation4568_implies_Equation4436 (G : Type*) [Magma G] (h : Equation4568 G) : Equation4436 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X1 ◇ X2)) ◇ X0) = (X4 ◇ ((X3 ◇ X2) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X1)) = (X4 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq70 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK0)) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1 in 19
  have eq293 (X1 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ (X3 ◇ X4)) = (X6 ◇ ((X7 ◇ X2) ◇ X1)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1 in 11
  have eq354 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ X2) ◇ X1)) ≠ (X5 ◇ (sK1 ◇ sK0)) := superpose eq11 eq70 -- superposition 70,11, 11 into 70, unify on (0).2 in 11 and (0).1 in 70
  subsumption eq354 eq293


