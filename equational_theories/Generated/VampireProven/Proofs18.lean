import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation2920_implies_Equation2311 (G : Type*) [Magma G] (h : Equation2920 G) : Equation2311 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK1) := mod_symm nh
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
  have eq83 : sK0 ≠ ((sK1 ◇ sK2) ◇ sK1) := superpose eq68 eq10 -- backward demodulation 10,68
  have eq84 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq71 eq72 -- forward demodulation 72,71
  have eq97 (X0 X1 : G) : X0 = X1 := superpose eq17 eq84 -- superposition 84,17, 17 into 84, unify on (0).2 in 17 and (0).1 in 84
  have eq106 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq84 eq83 -- superposition 83,84, 84 into 83, unify on (0).2 in 84 and (0).2 in 83
  subsumption eq106 eq97


@[equational_result]
theorem Equation2920_implies_Equation2947 (G : Type*) [Magma G] (h : Equation2920 G) : Equation2947 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.2 in 13
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2.2 in 13
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) = (X1 ◇ ((((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X5)) ◇ (X0 ◇ X1))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq33 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).1.2.2 in 13
  have eq38 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1))) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.1 in 17
  have eq52 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq16 eq38 -- forward demodulation 38,16
  have eq54 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = (X1 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X5)) ◇ (X0 ◇ X1))) := superpose eq52 eq22 -- backward demodulation 22,52
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1) = X0 := superpose eq52 eq9 -- backward demodulation 9,52
  have eq61 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq52 eq16 -- backward demodulation 16,52
  have eq66 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = (X1 ◇ ((X0 ◇ X1) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X5)))) := superpose eq52 eq54 -- forward demodulation 54,52
  have eq68 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq33 eq61 -- forward demodulation 61,33
  have eq72 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) := superpose eq68 eq66 -- backward demodulation 66,68
  have eq82 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq68 eq58 -- backward demodulation 58,68
  have eq83 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq68 eq10 -- backward demodulation 10,68
  have eq85 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq68 eq72 -- forward demodulation 72,68
  have eq86 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq33 eq85 -- forward demodulation 85,33
  have eq87 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq86 eq83 -- forward demodulation 83,86
  subsumption eq87 eq82


@[equational_result]
theorem Equation2920_implies_Equation1151 (G : Type*) [Magma G] (h : Equation2920 G) : Equation1151 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.2 in 13
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2.2 in 13
  have eq33 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).1.2.2 in 13
  have eq38 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1))) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.1 in 17
  have eq52 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq16 eq38 -- forward demodulation 38,16
  have eq61 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq52 eq16 -- backward demodulation 16,52
  have eq68 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq33 eq61 -- forward demodulation 61,33
  have eq83 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq68 eq10 -- backward demodulation 10,68
  subsumption eq83 eq68


@[equational_result]
theorem Equation2920_implies_Equation2721 (G : Type*) [Magma G] (h : Equation2920 G) : Equation2721 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK2 ◇ sK1)) ◇ sK1) := mod_symm nh
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
  have eq83 : sK0 ≠ (sK2 ◇ sK1) := superpose eq68 eq10 -- backward demodulation 10,68
  have eq84 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq71 eq72 -- forward demodulation 72,71
  have eq97 (X0 X1 : G) : X0 = X1 := superpose eq17 eq84 -- superposition 84,17, 17 into 84, unify on (0).2 in 17 and (0).1 in 84
  have eq106 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq84 eq83 -- superposition 83,84, 84 into 83, unify on (0).2 in 84 and (0).2 in 83
  subsumption eq106 eq97


@[equational_result]
theorem Equation2920_implies_Equation445 (G : Type*) [Magma G] (h : Equation2920 G) : Equation445 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := mod_symm nh
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
  have eq83 : sK0 ≠ (sK0 ◇ sK1) := superpose eq68 eq10 -- backward demodulation 10,68
  have eq84 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq71 eq72 -- forward demodulation 72,71
  have eq97 (X0 X1 : G) : X0 = X1 := superpose eq17 eq84 -- superposition 84,17, 17 into 84, unify on (0).2 in 17 and (0).1 in 84
  have eq106 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq84 eq83 -- superposition 83,84, 84 into 83, unify on (0).2 in 84 and (0).2 in 83
  subsumption eq106 eq97


@[equational_result]
theorem Equation2920_implies_Equation2729 (G : Type*) [Magma G] (h : Equation2920 G) : Equation2729 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK2 ◇ sK3)) ◇ sK1) := mod_symm nh
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
  have eq83 : sK0 ≠ (sK2 ◇ sK1) := superpose eq68 eq10 -- backward demodulation 10,68
  have eq84 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq71 eq72 -- forward demodulation 72,71
  have eq97 (X0 X1 : G) : X0 = X1 := superpose eq17 eq84 -- superposition 84,17, 17 into 84, unify on (0).2 in 17 and (0).1 in 84
  have eq106 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq84 eq83 -- superposition 83,84, 84 into 83, unify on (0).2 in 84 and (0).2 in 83
  subsumption eq106 eq97


@[equational_result]
theorem Equation1522_implies_Equation2920 (G : Type*) [Magma G] (h : Equation1522 G) : Equation2920 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq37 (X1 X2 : G) : X1 = X2 := superpose eq16 eq16 -- superposition 16,16, 16 into 16, unify on (0).2 in 16 and (0).1 in 16
  have eq61 (X0 : G) : sK0 ≠ ((X0 ◇ X0) ◇ sK1) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1 in 10
  subsumption eq61 eq37


@[equational_result]
theorem Equation1522_implies_Equation2937 (G : Type*) [Magma G] (h : Equation1522 G) : Equation2937 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq37 (X1 X2 : G) : X1 = X2 := superpose eq16 eq16 -- superposition 16,16, 16 into 16, unify on (0).2 in 16 and (0).1 in 16
  have eq49 (X0 : G) : sK0 ≠ (((sK1 ◇ (X0 ◇ X0)) ◇ sK0) ◇ sK1) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1.1.2 in 10
  subsumption eq49 eq37


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
theorem Equation2717_implies_Equation2686 (G : Type*) [Magma G] (h : Equation2717 G) : Equation2686 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X3 ◇ X0) ◇ X1) ◇ X3) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq27 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq34 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK3) := superpose eq27 eq10 -- backward demodulation 10,27
  have eq41 (X2 X3 : G) : X2 = X3 := superpose eq17 eq17 -- superposition 17,17, 17 into 17, unify on (0).2 in 17 and (0).1 in 17
  have eq54 (X0 X1 : G) : sK0 ≠ ((X0 ◇ (X1 ◇ X0)) ◇ sK3) := superpose eq17 eq34 -- superposition 34,17, 17 into 34, unify on (0).2 in 17 and (0).2.1 in 34
  subsumption eq54 eq41


@[equational_result]
theorem Equation2717_implies_Equation2112 (G : Type*) [Magma G] (h : Equation2717 G) : Equation2112 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK2) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X3 ◇ X0) ◇ X1) ◇ X3) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq27 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq34 : sK0 ≠ ((sK2 ◇ sK2) ◇ (sK1 ◇ sK1)) := superpose eq27 eq10 -- backward demodulation 10,27
  have eq41 (X2 X3 : G) : X2 = X3 := superpose eq17 eq17 -- superposition 17,17, 17 into 17, unify on (0).2 in 17 and (0).1 in 17
  have eq54 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X1 ◇ X0)) := superpose eq17 eq34 -- superposition 34,17, 17 into 34, unify on (0).2 in 17 and (0).2 in 34
  subsumption eq54 eq41


@[equational_result]
theorem Equation2976_implies_Equation464 (G : Type*) [Magma G] (h : Equation2976 G) : Equation464 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq11 (X2 X3 X4 X5 : G) : (((X4 ◇ X2) ◇ X3) ◇ X5) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X2 X4 X5 : G) : ((X2 ◇ X4) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 (X2 X3 X5 : G) : (X2 ◇ X5) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq16 (X2 X3 : G) : X2 = X3 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq18 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ X0))) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2.2.2 in 10
  subsumption eq18 eq16


@[equational_result]
theorem Equation2976_implies_Equation1500 (G : Type*) [Magma G] (h : Equation2976 G) : Equation1500 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq11 (X2 X3 X4 X5 : G) : (((X4 ◇ X2) ◇ X3) ◇ X5) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X2 X4 X5 : G) : ((X2 ◇ X4) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 (X2 X3 X5 : G) : (X2 ◇ X5) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq16 (X2 X3 : G) : X2 = X3 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq18 eq16


@[equational_result]
theorem Equation494_implies_Equation1282 (G : Type*) [Magma G] (h : Equation494 G) : Equation1282 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK0) ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X1))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq15 (X2 X3 : G) : X2 = X3 := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq17 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2.1 in 10
  subsumption eq17 eq15


@[equational_result]
theorem Equation2906_implies_Equation494 (G : Type*) [Magma G] (h : Equation2906 G) : Equation494 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq25 (X0 X1 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq25 eq17


@[equational_result]
theorem Equation2906_implies_Equation2916 (G : Type*) [Magma G] (h : Equation2906 G) : Equation2916 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq25 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq25 eq17


@[equational_result]
theorem Equation2906_implies_Equation3194 (G : Type*) [Magma G] (h : Equation2906 G) : Equation3194 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK2) ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq23 (X0 X1 : G) : sK0 ≠ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq23 eq17


@[equational_result]
theorem Equation2906_implies_Equation3478 (G : Type*) [Magma G] (h : Equation2906 G) : Equation3478 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK0 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq25 (X0 X1 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq25 eq14


@[equational_result]
theorem Equation751_implies_Equation2932 (G : Type*) [Magma G] (h : Equation751 G) : Equation2932 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK2)) ◇ sK3) ◇ sK1) := mod_symm nh
  have eq13 (X1 X2 X4 : G) : (X4 ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X2 X4 : G) : X2 = X4 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq20 (X0 : G) : sK0 ≠ (X0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq20 eq14


@[equational_result]
theorem Equation751_implies_Equation693 (G : Type*) [Magma G] (h : Equation751 G) : Equation693 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK2 ◇ sK1) ◇ sK3))) := mod_symm nh
  have eq13 (X1 X2 X4 : G) : (X4 ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X2 X4 : G) : X2 = X4 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq20 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ X0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.2 in 10
  subsumption eq20 eq14


@[equational_result]
theorem Equation2991_implies_Equation1449 (G : Type*) [Magma G] (h : Equation2991 G) : Equation1449 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq16 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq20 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq16 eq15 -- backward demodulation 15,16
  have eq23 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq23 eq20


@[equational_result]
theorem Equation2991_implies_Equation1722 (G : Type*) [Magma G] (h : Equation2991 G) : Equation1722 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq16 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq20 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq16 eq15 -- backward demodulation 15,16
  have eq23 (X2 X3 : G) : X2 = X3 := superpose eq11 eq20 -- superposition 20,11, 11 into 20, unify on (0).2 in 11 and (0).1 in 20
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq29 eq23


@[equational_result]
theorem Equation2991_implies_Equation1706 (G : Type*) [Magma G] (h : Equation2991 G) : Equation1706 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq16 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq20 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq16 eq15 -- backward demodulation 15,16
  have eq23 (X2 X3 : G) : X2 = X3 := superpose eq11 eq20 -- superposition 20,11, 11 into 20, unify on (0).2 in 11 and (0).1 in 20
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq29 eq23


@[equational_result]
theorem Equation2991_implies_Equation271 (G : Type*) [Magma G] (h : Equation2991 G) : Equation271 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2991_implies_Equation501 (G : Type*) [Magma G] (h : Equation2991 G) : Equation501 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq16 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq20 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq16 eq15 -- backward demodulation 15,16
  have eq23 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq23 eq20


@[equational_result]
theorem Equation277_implies_Equation1101 (G : Type*) [Magma G] (h : Equation277 G) : Equation1101 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X2 X3 : G) : X2 = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq20 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 eq16


@[equational_result]
theorem Equation277_implies_Equation467 (G : Type*) [Magma G] (h : Equation277 G) : Equation467 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X2 X3 : G) : X2 = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq23 (X0 X1 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2.2 in 10
  subsumption eq23 eq16


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
theorem Equation2010_implies_Equation277 (G : Type*) [Magma G] (h : Equation2010 G) : Equation277 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X4 ◇ X3) ◇ (X5 ◇ X4)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2)))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq21 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq15 eq12 -- backward demodulation 12,15
  have eq22 (X3 X4 : G) : X3 = X4 := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).1 in 21
  have eq26 (X0 : G) : sK0 ≠ ((X0 ◇ sK2) ◇ sK1) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2.1.1 in 10
  subsumption eq26 eq22


@[equational_result]
theorem Equation2010_implies_Equation913 (G : Type*) [Magma G] (h : Equation2010 G) : Equation913 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X4 ◇ X3) ◇ (X5 ◇ X4)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2)))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (sK1 ◇ sK2) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq22 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq16 eq12 -- backward demodulation 12,16
  have eq23 (X3 X4 : G) : X3 = X4 := superpose eq9 eq22 -- superposition 22,9, 9 into 22, unify on (0).2 in 9 and (0).1 in 22
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq14 -- superposition 14,22, 22 into 14, unify on (0).2 in 22 and (0).2 in 14
  subsumption eq34 eq23


@[equational_result]
theorem Equation2010_implies_Equation1994 (G : Type*) [Magma G] (h : Equation2010 G) : Equation1994 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X4 ◇ X3) ◇ (X5 ◇ X4)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2)))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq21 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq15 eq12 -- backward demodulation 12,15
  have eq22 (X3 X4 : G) : X3 = X4 := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).1 in 21
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq31 eq22


@[equational_result]
theorem Equation2010_implies_Equation2575 (G : Type*) [Magma G] (h : Equation2010 G) : Equation2575 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK0) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X4 ◇ X3) ◇ (X5 ◇ X4)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2)))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq21 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq15 eq12 -- backward demodulation 12,15
  have eq22 (X3 X4 : G) : X3 = X4 := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).1 in 21
  have eq31 (X0 : G) : sK0 ≠ ((sK1 ◇ X0) ◇ sK0) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2.1.2 in 10
  subsumption eq31 eq22


@[equational_result]
theorem Equation3119_implies_Equation3117 (G : Type*) [Magma G] (h : Equation3119 G) : Equation3117 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq15 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq19 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq22 (X1 X2 : G) : X1 = X2 := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1 in 15
  have eq27 (X0 : G) : sK0 ≠ (X0 ◇ sK2) := superpose eq15 eq19 -- superposition 19,15, 15 into 19, unify on (0).2 in 15 and (0).2.1 in 19
  subsumption eq27 eq22


@[equational_result]
theorem Equation3119_implies_Equation522 (G : Type*) [Magma G] (h : Equation3119 G) : Equation522 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq22 (X1 X2 : G) : X1 = X2 := superpose eq12 eq17 -- superposition 17,12, 12 into 17, unify on (0).2 in 12 and (0).1 in 17
  have eq27 (X0 : G) : sK0 ≠ (sK1 ◇ X0) := superpose eq17 eq13 -- superposition 13,17, 17 into 13, unify on (0).2 in 17 and (0).2.2 in 13
  subsumption eq27 eq22


@[equational_result]
theorem Equation3119_implies_Equation1698 (G : Type*) [Magma G] (h : Equation3119 G) : Equation1698 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq15 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq18 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq20 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK2) := superpose eq18 eq10 -- backward demodulation 10,18
  have eq22 (X1 X2 : G) : X1 = X2 := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1 in 15
  have eq27 (X0 : G) : sK0 ≠ (X0 ◇ sK2) := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).2.1 in 20
  subsumption eq27 eq22


@[equational_result]
theorem Equation3027_implies_Equation3119 (G : Type*) [Magma G] (h : Equation3027 G) : Equation3119 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK1) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X2 X3 X4 X5 : G) : (((X4 ◇ X3) ◇ X5) ◇ X2) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X3 X4 X5 : G) : ((X4 ◇ X5) ◇ X3) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 : sK0 ≠ (sK1 ◇ sK1) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq15 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq19 (X2 X3 : G) : X2 = X3 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq21 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq19 eq14 -- superposition 14,19, 19 into 14, unify on (0).2 in 19 and (0).2.1 in 14
  subsumption eq21 eq19


@[equational_result]
theorem Equation3027_implies_Equation1870 (G : Type*) [Magma G] (h : Equation3027 G) : Equation1870 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK3)) := mod_symm nh
  have eq11 (X2 X3 X4 X5 : G) : (((X4 ◇ X3) ◇ X5) ◇ X2) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X3 X4 X5 : G) : ((X4 ◇ X5) ◇ X3) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 (X2 X3 X5 : G) : (X3 ◇ X2) = X5 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq16 (X2 X3 : G) : X2 = X3 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq18 eq16


@[equational_result]
theorem Equation3027_implies_Equation222 (G : Type*) [Magma G] (h : Equation3027 G) : Equation222 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X2 X3 X4 X5 : G) : (((X4 ◇ X3) ◇ X5) ◇ X2) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X3 X4 X5 : G) : ((X4 ◇ X5) ◇ X3) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 (X2 X3 X5 : G) : (X3 ◇ X2) = X5 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq16 (X2 X3 : G) : X2 = X3 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq18 eq16


@[equational_result]
theorem Equation3027_implies_Equation3135 (G : Type*) [Magma G] (h : Equation3027 G) : Equation3135 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK2) ◇ sK3) ◇ sK1) := mod_symm nh
  have eq11 (X2 X3 X4 X5 : G) : (((X4 ◇ X3) ◇ X5) ◇ X2) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X3 X4 X5 : G) : ((X4 ◇ X5) ◇ X3) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 : sK0 ≠ (sK2 ◇ sK1) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq15 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq19 (X2 X3 : G) : X2 = X3 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq21 (X0 : G) : sK0 ≠ (X0 ◇ sK1) := superpose eq19 eq14 -- superposition 14,19, 19 into 14, unify on (0).2 in 19 and (0).2.1 in 14
  subsumption eq21 eq19


@[equational_result]
theorem Equation291_implies_Equation1280 (G : Type*) [Magma G] (h : Equation291 G) : Equation1280 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq19 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq19 eq15


@[equational_result]
theorem Equation291_implies_Equation67 (G : Type*) [Magma G] (h : Equation291 G) : Equation67 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ (sK1 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).2 in 13
  subsumption eq25 eq16


@[equational_result]
theorem Equation1290_implies_Equation451 (G : Type*) [Magma G] (h : Equation1290 G) : Equation451 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X1 X3 : G) : X1 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq20 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation1290_implies_Equation961 (G : Type*) [Magma G] (h : Equation1290 G) : Equation961 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X1 X3 : G) : X1 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq19 (X0 : G) : sK0 ≠ (sK1 ◇ X0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq19 eq13


@[equational_result]
theorem Equation1290_implies_Equation3103 (G : Type*) [Magma G] (h : Equation1290 G) : Equation3103 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X1 X3 : G) : X1 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq20 (X0 : G) : sK0 ≠ (((X0 ◇ sK0) ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1.1.1 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation1290_implies_Equation1703 (G : Type*) [Magma G] (h : Equation1290 G) : Equation1703 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X1 X3 : G) : X1 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq19 eq13


@[equational_result]
theorem Equation1714_implies_Equation2328 (G : Type*) [Magma G] (h : Equation1714 G) : Equation2328 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1) := mod_symm nh
  have eq12 (X1 X4 X5 : G) : ((X4 ◇ X5) ◇ (X1 ◇ X4)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ X3) ◇ X0) ◇ X4) ◇ X1) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ X1) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq21 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq17 eq13 -- backward demodulation 13,17
  have eq22 (X1 X4 : G) : X1 = X4 := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).1 in 21
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq30 eq22


@[equational_result]
theorem Equation1714_implies_Equation1290 (G : Type*) [Magma G] (h : Equation1714 G) : Equation1290 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X1 X4 X5 : G) : ((X4 ◇ X5) ◇ (X1 ◇ X4)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ X3) ◇ X0) ◇ X4) ◇ X1) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ X1) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq21 : sK0 ≠ (sK1 ◇ sK1) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq22 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq17 eq13 -- backward demodulation 13,17
  have eq23 (X1 X4 : G) : X1 = X4 := superpose eq9 eq22 -- superposition 22,9, 9 into 22, unify on (0).2 in 9 and (0).1 in 22
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq21 -- superposition 21,22, 22 into 21, unify on (0).2 in 22 and (0).2 in 21
  subsumption eq34 eq23


@[equational_result]
theorem Equation1714_implies_Equation1292 (G : Type*) [Magma G] (h : Equation1714 G) : Equation1292 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK1) ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq12 (X1 X4 X5 : G) : ((X4 ◇ X5) ◇ (X1 ◇ X4)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ X3) ◇ X0) ◇ X4) ◇ X1) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ X1) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq21 : sK0 ≠ (sK1 ◇ sK2) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq22 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq17 eq13 -- backward demodulation 13,17
  have eq23 (X1 X4 : G) : X1 = X4 := superpose eq9 eq22 -- superposition 22,9, 9 into 22, unify on (0).2 in 9 and (0).1 in 22
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq21 -- superposition 21,22, 22 into 21, unify on (0).2 in 22 and (0).2 in 21
  subsumption eq34 eq23


@[equational_result]
theorem Equation1714_implies_Equation2906 (G : Type*) [Magma G] (h : Equation1714 G) : Equation2906 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X1 X4 X5 : G) : ((X4 ◇ X5) ◇ (X1 ◇ X4)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ X3) ◇ X0) ◇ X4) ◇ X1) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ X1) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq21 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq17 eq13 -- backward demodulation 13,17
  have eq22 (X1 X4 : G) : X1 = X4 := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).1 in 21
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq33 eq22


@[equational_result]
theorem Equation1714_implies_Equation2109 (G : Type*) [Magma G] (h : Equation1714 G) : Equation2109 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK2) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X1 X4 X5 : G) : ((X4 ◇ X5) ◇ (X1 ◇ X4)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ X3) ◇ X0) ◇ X4) ◇ X1) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ X1) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq21 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq17 eq13 -- backward demodulation 13,17
  have eq22 (X1 X4 : G) : X1 = X4 := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).1 in 21
  have eq30 (X0 : G) : sK0 ≠ (X0 ◇ (sK0 ◇ sK2)) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2.1 in 10
  subsumption eq30 eq22


@[equational_result]
theorem Equation1714_implies_Equation14 (G : Type*) [Magma G] (h : Equation1714 G) : Equation14 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X4 X5 : G) : ((X4 ◇ X5) ◇ (X1 ◇ X4)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ X3) ◇ X0) ◇ X4) ◇ X1) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ X1) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq21 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq17 eq13 -- backward demodulation 13,17
  have eq22 (X1 X4 : G) : X1 = X4 := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).1 in 21
  have eq33 (X0 : G) : sK0 ≠ (sK1 ◇ X0) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2.2 in 10
  subsumption eq33 eq22


@[equational_result]
theorem Equation1714_implies_Equation3160 (G : Type*) [Magma G] (h : Equation1714 G) : Equation3160 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK2) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X1 X4 X5 : G) : ((X4 ◇ X5) ◇ (X1 ◇ X4)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ X3) ◇ X0) ◇ X4) ◇ X1) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ X1) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq21 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq17 eq13 -- backward demodulation 13,17
  have eq22 : sK0 ≠ (sK2 ◇ sK1) := superpose eq17 eq10 -- backward demodulation 10,17
  subsumption eq22 eq21


@[equational_result]
theorem Equation3109_implies_Equation1492 (G : Type*) [Magma G] (h : Equation3109 G) : Equation1492 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq20 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq15 eq9 -- backward demodulation 9,15
  have eq23 : sK0 ≠ (sK1 ◇ sK1) := superpose eq15 eq14 -- backward demodulation 14,15
  have eq28 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq15 eq20 -- forward demodulation 20,15
  have eq29 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq15 eq28 -- forward demodulation 28,15
  subsumption eq23 eq29


@[equational_result]
theorem Equation3109_implies_Equation1714 (G : Type*) [Magma G] (h : Equation3109 G) : Equation1714 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK3) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq21 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X0 := superpose eq14 eq9 -- backward demodulation 9,14
  have eq22 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK3)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq28 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq14 eq21 -- forward demodulation 21,14
  have eq29 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq14 eq28 -- forward demodulation 28,14
  have eq30 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK2) := superpose eq14 eq22 -- forward demodulation 22,14
  have eq31 : sK0 ≠ (sK1 ◇ sK2) := superpose eq14 eq30 -- forward demodulation 30,14
  have eq35 (X1 X2 : G) : X1 = X2 := superpose eq29 eq29 -- superposition 29,29, 29 into 29, unify on (0).2 in 29 and (0).1 in 29
  have eq37 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq29 eq31 -- superposition 31,29, 29 into 31, unify on (0).2 in 29 and (0).2 in 31
  subsumption eq37 eq35


@[equational_result]
theorem Equation3109_implies_Equation2166 (G : Type*) [Magma G] (h : Equation3109 G) : Equation2166 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq19 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq14 eq9 -- backward demodulation 9,14
  have eq21 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq27 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq14 eq19 -- forward demodulation 19,14
  have eq28 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq14 eq27 -- forward demodulation 27,14
  have eq30 : sK0 ≠ ((sK1 ◇ sK2) ◇ sK1) := superpose eq14 eq21 -- forward demodulation 21,14
  have eq31 : sK0 ≠ (sK1 ◇ sK1) := superpose eq14 eq30 -- forward demodulation 30,14
  subsumption eq31 eq28


@[equational_result]
theorem Equation3109_implies_Equation2924 (G : Type*) [Magma G] (h : Equation3109 G) : Equation2924 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK2)) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq21 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X0 := superpose eq14 eq9 -- backward demodulation 9,14
  have eq22 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq28 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq14 eq21 -- forward demodulation 21,14
  have eq29 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq14 eq28 -- forward demodulation 28,14
  have eq30 : sK0 ≠ (sK1 ◇ sK1) := superpose eq14 eq22 -- forward demodulation 22,14
  subsumption eq30 eq29


@[equational_result]
theorem Equation1350_implies_Equation3109 (G : Type*) [Magma G] (h : Equation1350 G) : Equation3109 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK0) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = (X3 ◇ ((X2 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X3) ◇ X3) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X1 X2 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X2)) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq22 (X1 X3 X4 : G) : (X4 ◇ ((X3 ◇ X1) ◇ X4)) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1.1 in 9
  have eq42 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X3)) ◇ X0) = (((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X3)) ◇ X0) ◇ ((((X2 ◇ X1) ◇ X1) ◇ X3) ◇ ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X3)) ◇ X0))) := superpose eq11 eq19 -- superposition 19,11, 11 into 19, unify on (0).2 in 11 and (0).1.2.1 in 19
  have eq55 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X3)) ◇ X0) = X3 := superpose eq22 eq42 -- forward demodulation 42,22
  have eq56 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = (X3 ◇ X0) := superpose eq55 eq11 -- backward demodulation 11,55
  have eq67 (X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X2)) = X2 := superpose eq12 eq56 -- superposition 56,12, 12 into 56, unify on (0).2 in 12 and (0).1 in 56
  have eq108 (X1 X3 : G) : (X1 ◇ X3) = X1 := superpose eq67 eq12 -- backward demodulation 12,67
  have eq112 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq108 eq55 -- backward demodulation 55,108
  have eq127 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1) := superpose eq108 eq10 -- backward demodulation 10,108
  subsumption eq127 eq112


@[equational_result]
theorem Equation1350_implies_Equation493 (G : Type*) [Magma G] (h : Equation1350 G) : Equation493 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = (X3 ◇ ((X2 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X3) ◇ X3) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X1 X2 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X2)) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq23 (X1 X3 X4 : G) : (X4 ◇ ((X3 ◇ X1) ◇ X4)) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1.1 in 9
  have eq42 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X3)) ◇ X0) = (((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X3)) ◇ X0) ◇ ((((X2 ◇ X1) ◇ X1) ◇ X3) ◇ ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X3)) ◇ X0))) := superpose eq11 eq19 -- superposition 19,11, 11 into 19, unify on (0).2 in 11 and (0).1.2.1 in 19
  have eq44 (X1 X3 : G) : (X1 ◇ (X3 ◇ X1)) = X1 := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).1.2.1 in 19
  have eq55 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X3)) ◇ X0) = X3 := superpose eq23 eq42 -- forward demodulation 42,23
  have eq59 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK2)) := superpose eq44 eq10 -- backward demodulation 10,44
  have eq62 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq44 eq44 -- superposition 44,44, 44 into 44, unify on (0).2 in 44 and (0).1.2 in 44
  have eq63 (X1 X3 : G) : (X1 ◇ X3) = X1 := superpose eq12 eq44 -- superposition 44,12, 12 into 44, unify on (0).2 in 12 and (0).1.2 in 44
  have eq83 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X0) = X3 := superpose eq62 eq55 -- backward demodulation 55,62
  have eq89 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq63 eq83 -- backward demodulation 83,63
  have eq100 : sK0 ≠ (sK1 ◇ sK0) := superpose eq63 eq59 -- backward demodulation 59,63
  subsumption eq100 eq89


@[equational_result]
theorem Equation1350_implies_Equation2098 (G : Type*) [Magma G] (h : Equation1350 G) : Equation2098 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = (X3 ◇ ((X2 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X3) ◇ X3) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X1 X2 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X2)) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq23 (X1 X3 X4 : G) : (X4 ◇ ((X3 ◇ X1) ◇ X4)) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1.1 in 9
  have eq42 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X3)) ◇ X0) = (((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X3)) ◇ X0) ◇ ((((X2 ◇ X1) ◇ X1) ◇ X3) ◇ ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X3)) ◇ X0))) := superpose eq11 eq19 -- superposition 19,11, 11 into 19, unify on (0).2 in 11 and (0).1.2.1 in 19
  have eq55 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X3)) ◇ X0) = X3 := superpose eq23 eq42 -- forward demodulation 42,23
  have eq56 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = (X3 ◇ X0) := superpose eq55 eq11 -- backward demodulation 11,55
  have eq67 (X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X2)) = X2 := superpose eq12 eq56 -- superposition 56,12, 12 into 56, unify on (0).2 in 12 and (0).1 in 56
  have eq106 (X1 X3 : G) : (X1 ◇ X3) = X1 := superpose eq67 eq12 -- backward demodulation 12,67
  have eq110 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq106 eq55 -- backward demodulation 55,106
  have eq125 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := superpose eq106 eq10 -- backward demodulation 10,106
  subsumption eq125 eq110


@[equational_result]
theorem Equation1350_implies_Equation115 (G : Type*) [Magma G] (h : Equation1350 G) : Equation115 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = (X3 ◇ ((X2 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X3) ◇ X3) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X1 X2 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X2)) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq23 (X1 X3 X4 : G) : (X4 ◇ ((X3 ◇ X1) ◇ X4)) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1.1 in 9
  have eq42 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X3)) ◇ X0) = (((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X3)) ◇ X0) ◇ ((((X2 ◇ X1) ◇ X1) ◇ X3) ◇ ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X3)) ◇ X0))) := superpose eq11 eq19 -- superposition 19,11, 11 into 19, unify on (0).2 in 11 and (0).1.2.1 in 19
  have eq55 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X3)) ◇ X0) = X3 := superpose eq23 eq42 -- forward demodulation 42,23
  have eq56 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = (X3 ◇ X0) := superpose eq55 eq11 -- backward demodulation 11,55
  have eq67 (X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X2)) = X2 := superpose eq12 eq56 -- superposition 56,12, 12 into 56, unify on (0).2 in 12 and (0).1 in 56
  have eq105 (X1 X3 : G) : (X1 ◇ X3) = X1 := superpose eq67 eq12 -- backward demodulation 12,67
  have eq109 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq105 eq55 -- backward demodulation 55,105
  have eq124 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq105 eq10 -- backward demodulation 10,105
  subsumption eq124 eq109


@[equational_result]
theorem Equation3569_implies_Equation3957 (G : Type*) [Magma G] (h : Equation3569 G) : Equation3957 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X1) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X0) ◇ X2)) = (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X1 ◇ X0) ◇ X2))) = (((X2 ◇ X0) ◇ X3) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1 in 12
  have eq19 (X1 X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X2)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq20 (X1 X2 X3 X4 : G) : (X4 ◇ X2) = (X2 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X2))) ◇ X4)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2.1 in 9
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X5) ◇ ((X2 ◇ X1) ◇ X3)) = (((X2 ◇ X1) ◇ X3) ◇ (X5 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1.2 in 12
  have eq45 (X0 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.2.2 in 19
  have eq50 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq19 eq19 -- superposition 19,19, 19 into 19, unify on (0).2 in 19 and (0).2.2 in 19
  have eq52 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq83 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X1) ◇ X4) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X4 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))))) := superpose eq11 eq20 -- superposition 20,11, 11 into 20, unify on (0).2 in 11 and (0).2.2 in 20
  have eq86 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X4 ◇ X3))) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq19 eq20 -- superposition 20,19, 19 into 20, unify on (0).2 in 19 and (0).2.2 in 20
  have eq89 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3))) = (((X3 ◇ X0) ◇ X4) ◇ X3) := superpose eq20 eq12 -- superposition 12,20, 20 into 12, unify on (0).2 in 20 and (0).1.1.1 in 12
  have eq90 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X3 ◇ X0) ◇ X0)) := superpose eq20 eq19 -- superposition 19,20, 20 into 19, unify on (0).2 in 20 and (0).2.2 in 19
  have eq112 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq19 eq45 -- superposition 45,19, 19 into 45, unify on (0).2 in 19 and (0).2.2 in 45
  have eq118 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq45 eq19 -- superposition 19,45, 45 into 19, unify on (0).2 in 45 and (0).2.2 in 19
  have eq122 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) = (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) := superpose eq45 eq12 -- superposition 12,45, 45 into 12, unify on (0).2 in 45 and (0).1.1.1 in 12
  have eq126 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) = (((X3 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq45 eq11 -- superposition 11,45, 45 into 11, unify on (0).2 in 45 and (0).2.2.1 in 11
  have eq127 (X0 X1 X2 X3 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X3) ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq45 eq12 -- superposition 12,45, 45 into 12, unify on (0).2 in 45 and (0).1.1.1.2 in 12
  have eq131 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ (X0 ◇ X1))) ◇ ((X3 ◇ X1) ◇ X0)) = (((X3 ◇ X1) ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq45 eq11 -- superposition 11,45, 45 into 11, unify on (0).2 in 45 and (0).2.2 in 11
  have eq133 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = ((X2 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) := superpose eq45 eq9 -- superposition 9,45, 45 into 9, unify on (0).2 in 45 and (0).2.2 in 9
  have eq136 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq50 eq112 -- forward demodulation 112,50
  have eq141 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X3 ◇ X0) ◇ X0)) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq118 eq90 -- backward demodulation 90,118
  have eq143 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq118 eq122 -- forward demodulation 122,118
  have eq147 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X0)) = (((X3 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq118 eq126 -- forward demodulation 126,118
  have eq148 (X0 X1 X2 X3 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X3) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq118 eq127 -- forward demodulation 127,118
  have eq151 (X0 X1 X2 X3 : G) : (((X3 ◇ X1) ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X2) ◇ ((X3 ◇ X1) ◇ X0)) := superpose eq118 eq131 -- forward demodulation 131,118
  have eq153 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq118 eq133 -- forward demodulation 133,118
  have eq164 (X1 X2 X3 X4 : G) : (X2 ◇ (X4 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X2))))) = (((X2 ◇ X3) ◇ X4) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2.2 in 15
  have eq170 (X0 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (((X2 ◇ X0) ◇ X0) ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).1.2 in 15
  have eq175 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ X3) ◇ ((X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X5)) ◇ X4) = (X4 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X5 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))))) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2 in 15
  have eq209 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X4 ◇ X3))) ◇ X0) = (((X0 ◇ X1) ◇ X3) ◇ X0) := superpose eq164 eq86 -- backward demodulation 86,164
  have eq212 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X1) ◇ X4) ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X2) ◇ X4) ◇ (X0 ◇ X1)) := superpose eq164 eq83 -- backward demodulation 83,164
  have eq216 (X0 X2 : G) : (X0 ◇ X2) = (((X2 ◇ X0) ◇ X0) ◇ X2) := superpose eq118 eq170 -- forward demodulation 170,118
  have eq222 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ X3) ◇ ((X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X5)) ◇ X4) = ((X5 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X4) := superpose eq9 eq175 -- forward demodulation 175,9
  have eq223 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq9 eq118 -- superposition 118,9, 9 into 118, unify on (0).2 in 9 and (0).2.2 in 118
  have eq227 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq118 eq118 -- superposition 118,118, 118 into 118, unify on (0).2 in 118 and (0).2.2 in 118
  have eq229 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) = (((X2 ◇ X1) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq11 eq118 -- superposition 118,11, 11 into 118, unify on (0).2 in 11 and (0).2.2 in 118
  have eq230 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq19 eq118 -- superposition 118,19, 19 into 118, unify on (0).2 in 19 and (0).2 in 118
  have eq251 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = (X2 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X1 ◇ X2))) := superpose eq118 eq12 -- superposition 12,118, 118 into 12, unify on (0).2 in 118 and (0).1.1 in 12
  have eq253 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ X1)) := superpose eq223 eq153 -- backward demodulation 153,223
  have eq257 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ X0) = ((X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3)) ◇ X0) := superpose eq253 eq209 -- backward demodulation 209,253
  have eq258 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ X1)) := superpose eq253 eq12 -- backward demodulation 12,253
  have eq267 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq253 eq52 -- backward demodulation 52,253
  have eq274 (X0 X1 X3 X4 : G) : (((X3 ◇ X0) ◇ X4) ◇ X3) = (X3 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3))) := superpose eq253 eq89 -- backward demodulation 89,253
  have eq282 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X3 ◇ X0) ◇ X0)) := superpose eq253 eq141 -- backward demodulation 141,253
  have eq296 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ X0) = ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X0) := superpose eq253 eq257 -- forward demodulation 257,253
  have eq298 (X0 X3 X4 : G) : (((X3 ◇ X0) ◇ X4) ◇ X3) = (X3 ◇ (X4 ◇ X3)) := superpose eq253 eq274 -- forward demodulation 274,253
  have eq313 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X0)) = ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X0) := superpose eq298 eq296 -- backward demodulation 296,298
  have eq317 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X1) ◇ X4) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X4 ◇ (X0 ◇ X1))) := superpose eq298 eq212 -- backward demodulation 212,298
  have eq347 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ X0) := superpose eq230 eq267 -- backward demodulation 267,230
  have eq350 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ X1) := superpose eq347 eq50 -- backward demodulation 50,347
  have eq351 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq347 eq136 -- backward demodulation 136,347
  have eq352 (X0 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X0) ◇ X2) := superpose eq347 eq216 -- backward demodulation 216,347
  have eq353 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq347 eq282 -- backward demodulation 282,347
  have eq360 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq351 eq353 -- forward demodulation 353,351
  have eq375 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2)))) := superpose eq223 eq251 -- forward demodulation 251,223
  have eq376 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = ((X3 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq9 eq375 -- forward demodulation 375,9
  have eq377 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = (X2 ◇ X2) := superpose eq360 eq376 -- forward demodulation 376,360
  have eq379 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X4 ◇ (X0 ◇ X1))) = (((X1 ◇ X1) ◇ X4) ◇ (X0 ◇ X1)) := superpose eq377 eq317 -- backward demodulation 317,377
  have eq382 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ X3) ◇ ((X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X5)) ◇ X4) = (X4 ◇ X4) := superpose eq377 eq222 -- backward demodulation 222,377
  have eq383 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X4 ◇ (X0 ◇ X1))) = ((X1 ◇ X4) ◇ (X0 ◇ X1)) := superpose eq352 eq379 -- forward demodulation 379,352
  have eq384 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq383 eq229 -- backward demodulation 229,383
  have eq389 (X0 X1 X2 X3 : G) : (((X3 ◇ X1) ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) = ((X0 ◇ X2) ◇ ((X3 ◇ X1) ◇ X0)) := superpose eq384 eq151 -- backward demodulation 151,384
  have eq400 (X0 X1 X2 X3 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X3) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq118 eq258 -- superposition 258,118, 118 into 258, unify on (0).2 in 118 and (0).1.1.1.2 in 258
  have eq401 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X5) ◇ ((X2 ◇ X1) ◇ X3)) = (((X2 ◇ X1) ◇ X3) ◇ (X5 ◇ ((X2 ◇ X1) ◇ X3))) := superpose eq11 eq258 -- superposition 258,11, 11 into 258, unify on (0).2 in 11 and (0).1.1.1.2 in 258
  have eq419 (X0 X1 X2 X3 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X3) ◇ (X0 ◇ X1)) = ((X1 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq383 eq400 -- forward demodulation 400,383
  have eq420 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X1 ◇ X0))) = ((X1 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq419 eq148 -- backward demodulation 148,419
  have eq423 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) = ((X0 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq420 eq143 -- backward demodulation 143,420
  have eq424 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X5) ◇ ((X2 ◇ X1) ◇ X3)) = ((X3 ◇ X5) ◇ ((X2 ◇ X1) ◇ X3)) := superpose eq383 eq401 -- forward demodulation 401,383
  have eq425 (X0 X1 X2 X3 X5 : G) : (((X2 ◇ X1) ◇ X3) ◇ (X5 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2)))) = ((X3 ◇ X5) ◇ ((X2 ◇ X1) ◇ X3)) := superpose eq424 eq37 -- backward demodulation 37,424
  have eq498 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) := superpose eq11 eq352 -- superposition 352,11, 11 into 352, unify on (0).2 in 11 and (0).2.1 in 352
  have eq523 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq227 eq498 -- forward demodulation 498,227
  have eq524 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X0) ◇ X2) := superpose eq350 eq523 -- forward demodulation 523,350
  have eq525 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq352 eq524 -- forward demodulation 524,352
  have eq526 (X0 X3 : G) : (X3 ◇ X0) = (X0 ◇ (X3 ◇ X0)) := superpose eq525 eq313 -- backward demodulation 313,525
  have eq557 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq526 eq227 -- backward demodulation 227,526
  have eq584 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose eq526 eq525 -- backward demodulation 525,526
  have eq593 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = ((X0 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq557 eq423 -- backward demodulation 423,557
  have eq599 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X1) ◇ X0)) = (((X3 ◇ X1) ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq593 eq389 -- backward demodulation 389,593
  have eq603 (X0 X1 X2 X3 X5 : G) : (X5 ◇ ((X2 ◇ X1) ◇ X3)) = (((X2 ◇ X1) ◇ X3) ◇ (X5 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq593 eq425 -- backward demodulation 425,593
  have eq616 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq584 eq147 -- backward demodulation 147,584
  have eq630 (X0 X1 X3 X4 X5 : G) : (X4 ◇ X4) = (((X4 ◇ X3) ◇ ((X0 ◇ (X1 ◇ (X3 ◇ X4))) ◇ X5)) ◇ X4) := superpose eq584 eq382 -- backward demodulation 382,584
  have eq645 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq584 eq599 -- backward demodulation 599,584
  have eq648 (X1 X2 X3 X5 : G) : (X5 ◇ ((X2 ◇ X1) ◇ X3)) = (((X2 ◇ X1) ◇ X3) ◇ (X5 ◇ (X3 ◇ (X1 ◇ X2)))) := superpose eq584 eq603 -- backward demodulation 603,584
  have eq663 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) := superpose eq584 eq616 -- forward demodulation 616,584
  have eq664 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq584 eq663 -- forward demodulation 663,584
  have eq665 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X2)) := superpose eq557 eq664 -- forward demodulation 664,557
  have eq666 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X1 ◇ X0)) := superpose eq118 eq665 -- forward demodulation 665,118
  have eq670 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq666 eq593 -- backward demodulation 593,666
  have eq672 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK2) ◇ sK0) := superpose eq666 eq10 -- backward demodulation 10,666
  have eq695 (X3 X4 X5 : G) : (X4 ◇ X4) = (((X4 ◇ X3) ◇ X5) ◇ X4) := superpose eq666 eq630 -- forward demodulation 630,666
  have eq696 (X3 X4 X5 : G) : (X4 ◇ X4) = ((X3 ◇ X5) ◇ X4) := superpose eq584 eq695 -- forward demodulation 695,584
  have eq697 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq696 eq672 -- backward demodulation 672,696
  have eq708 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq666 eq645 -- forward demodulation 645,666
  have eq709 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ X0)) := superpose eq670 eq708 -- forward demodulation 708,670
  have eq710 (X1 X2 X3 X5 : G) : (X5 ◇ ((X2 ◇ X1) ◇ X3)) = (((X2 ◇ X1) ◇ X3) ◇ (X5 ◇ (X1 ◇ X2))) := superpose eq666 eq648 -- forward demodulation 648,666
  have eq711 (X1 X2 X3 X5 : G) : (X5 ◇ ((X2 ◇ X1) ◇ X3)) = ((X1 ◇ X2) ◇ X5) := superpose eq709 eq710 -- forward demodulation 710,709
  have eq712 (X1 X2 X3 X5 : G) : (X5 ◇ ((X2 ◇ X1) ◇ X3)) = (X2 ◇ X5) := superpose eq584 eq711 -- forward demodulation 711,584
  have eq713 (X1 X2 X3 X5 : G) : (X2 ◇ X5) = (X5 ◇ (X1 ◇ X3)) := superpose eq584 eq712 -- forward demodulation 712,584
  have eq800 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq118 eq713 -- superposition 713,118, 118 into 713, unify on (0).2 in 118 and (0).2 in 713
  have eq853 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X0) = (X4 ◇ (X1 ◇ X2)) := superpose eq713 eq800 -- superposition 800,713, 713 into 800, unify on (0).2 in 713 and (0).1 in 800
  have eq888 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK1) := superpose eq800 eq697 -- superposition 697,800, 800 into 697, unify on (0).2 in 800 and (0).1 in 697
  have eq941 (X1 X2 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X1 ◇ X2)) := superpose eq713 eq888 -- superposition 888,713, 713 into 888, unify on (0).2 in 713 and (0).2 in 888
  subsumption eq941 eq853


@[equational_result]
theorem Equation453_implies_Equation2042 (G : Type*) [Magma G] (h : Equation453 G) : Equation2042 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq14 eq16 -- forward demodulation 16,14
  have eq19 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq18 -- forward demodulation 18,14
  subsumption eq19 eq14


@[equational_result]
theorem Equation453_implies_Equation3930 (G : Type*) [Magma G] (h : Equation453 G) : Equation3930 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq18 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation453_implies_Equation1466 (G : Type*) [Magma G] (h : Equation453 G) : Equation1466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq18 : sK0 ≠ (sK0 ◇ sK2) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation453_implies_Equation3866 (G : Type*) [Magma G] (h : Equation453 G) : Equation3866 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq18 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation453_implies_Equation3672 (G : Type*) [Magma G] (h : Equation453 G) : Equation3672 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation453_implies_Equation3668 (G : Type*) [Magma G] (h : Equation453 G) : Equation3668 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation453_implies_Equation823 (G : Type*) [Magma G] (h : Equation453 G) : Equation823 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq16 eq14


@[equational_result]
theorem Equation453_implies_Equation3935 (G : Type*) [Magma G] (h : Equation453 G) : Equation3935 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq16 rfl


@[equational_result]
theorem Equation453_implies_Equation620 (G : Type*) [Magma G] (h : Equation453 G) : Equation620 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq16 eq14


@[equational_result]
theorem Equation453_implies_Equation3928 (G : Type*) [Magma G] (h : Equation453 G) : Equation3928 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq16 rfl


@[equational_result]
theorem Equation453_implies_Equation2085 (G : Type*) [Magma G] (h : Equation453 G) : Equation2085 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq17 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK3 ◇ sK3)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK3) := superpose eq14 eq17 -- forward demodulation 17,14
  have eq19 : sK0 ≠ (sK0 ◇ sK3) := superpose eq14 eq18 -- forward demodulation 18,14
  subsumption eq19 eq14


@[equational_result]
theorem Equation453_implies_Equation4395 (G : Type*) [Magma G] (h : Equation453 G) : Equation4395 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq18 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation453_implies_Equation3867 (G : Type*) [Magma G] (h : Equation453 G) : Equation3867 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq16 rfl


@[equational_result]
theorem Equation453_implies_Equation1246 (G : Type*) [Magma G] (h : Equation453 G) : Equation1246 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq17 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation453_implies_Equation1048 (G : Type*) [Magma G] (h : Equation453 G) : Equation1048 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq16 eq14


@[equational_result]
theorem Equation453_implies_Equation4 (G : Type*) [Magma G] (h : Equation453 G) : Equation4 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq17 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation453_implies_Equation4435 (G : Type*) [Magma G] (h : Equation453 G) : Equation4435 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq18 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation453_implies_Equation3 (G : Type*) [Magma G] (h : Equation453 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq11 eq8 -- backward demodulation 8,11
  have eq16 : sK0 ≠ sK0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2 in 9
  subsumption eq16 rfl


@[equational_result]
theorem Equation82_implies_Equation3921 (G : Type*) [Magma G] (h : Equation82 G) : Equation3921 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq21 eq14


@[equational_result]
theorem Equation82_implies_Equation1481 (G : Type*) [Magma G] (h : Equation82 G) : Equation1481 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq9


@[equational_result]
theorem Equation82_implies_Equation4689 (G : Type*) [Magma G] (h : Equation82 G) : Equation4689 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK3 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : ((sK0 ◇ sK1) ◇ sK2) ≠ (sK2 ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation2686_implies_Equation2077 (G : Type*) [Magma G] (h : Equation2686 G) : Equation2077 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X3 X4 X5 : G) : (((X4 ◇ X3) ◇ X0) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X4 : G) : (X0 ◇ X1) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq22 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ X0) ◇ (sK1 ◇ sK3)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq22 eq12


@[equational_result]
theorem Equation2499_implies_Equation3105 (G : Type*) [Magma G] (h : Equation2499 G) : Equation3105 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq25 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1 in 12
  have eq35 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq23 -- superposition 23,11, 11 into 23, unify on (0).2 in 11 and (0).1.1.2 in 23
  have eq36 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq23 -- superposition 23,9, 9 into 23, unify on (0).2 in 9 and (0).1.1 in 23
  have eq46 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq36 eq35 -- backward demodulation 35,36
  have eq48 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq36 eq25 -- backward demodulation 25,36
  have eq50 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq46 eq10 -- backward demodulation 10,46
  have eq63 : sK0 ≠ sK0 := superpose eq48 eq50 -- superposition 50,48, 48 into 50, unify on (0).2 in 48 and (0).2 in 50
  subsumption eq63 rfl


@[equational_result]
theorem Equation2499_implies_Equation2398 (G : Type*) [Magma G] (h : Equation2499 G) : Equation2398 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ X1) = ((X2 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq23 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1 in 12
  have eq35 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq23 -- superposition 23,11, 11 into 23, unify on (0).2 in 11 and (0).1.1.2 in 23
  have eq36 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq23 -- superposition 23,9, 9 into 23, unify on (0).2 in 9 and (0).1.1 in 23
  have eq46 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq36 eq35 -- backward demodulation 35,36
  have eq48 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq36 eq27 -- backward demodulation 27,36
  have eq49 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq36 eq20 -- backward demodulation 20,36
  have eq53 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq48 eq48 -- superposition 48,48, 48 into 48, unify on (0).2 in 48 and (0).1.1 in 48
  have eq62 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := superpose eq53 eq10 -- backward demodulation 10,53
  have eq99 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq46 eq49 -- superposition 49,46, 46 into 49, unify on (0).2 in 46 and (0).1 in 49
  have eq147 : sK0 ≠ sK0 := superpose eq99 eq62 -- superposition 62,99, 99 into 62, unify on (0).2 in 99 and (0).2 in 62
  subsumption eq147 rfl


@[equational_result]
theorem Equation2499_implies_Equation2322 (G : Type*) [Magma G] (h : Equation2499 G) : Equation2322 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq28 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2.1 in 9
  have eq36 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq23 -- superposition 23,9, 9 into 23, unify on (0).2 in 9 and (0).1.1 in 23
  have eq47 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq36 eq28 -- backward demodulation 28,36
  have eq79 : sK0 ≠ sK0 := superpose eq47 eq10 -- superposition 10,47, 47 into 10, unify on (0).2 in 47 and (0).2 in 10
  subsumption eq79 rfl


@[equational_result]
theorem Equation2499_implies_Equation3108 (G : Type*) [Magma G] (h : Equation2499 G) : Equation3108 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK0) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq25 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1 in 12
  have eq35 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq23 -- superposition 23,11, 11 into 23, unify on (0).2 in 11 and (0).1.1.2 in 23
  have eq36 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq23 -- superposition 23,9, 9 into 23, unify on (0).2 in 9 and (0).1.1 in 23
  have eq46 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq36 eq35 -- backward demodulation 35,36
  have eq48 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq36 eq25 -- backward demodulation 25,36
  have eq50 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK0) := superpose eq46 eq10 -- backward demodulation 10,46
  have eq63 : sK0 ≠ sK0 := superpose eq48 eq50 -- superposition 50,48, 48 into 50, unify on (0).2 in 48 and (0).2 in 50
  subsumption eq63 rfl


@[equational_result]
theorem Equation2499_implies_Equation2652 (G : Type*) [Magma G] (h : Equation2499 G) : Equation2652 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation2499_implies_Equation1647 (G : Type*) [Magma G] (h : Equation2499 G) : Equation1647 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1 in 12
  have eq36 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq23 -- superposition 23,9, 9 into 23, unify on (0).2 in 9 and (0).1.1 in 23
  have eq48 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq36 eq27 -- backward demodulation 27,36
  have eq50 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq48 eq10 -- backward demodulation 10,48
  subsumption eq50 eq48


@[equational_result]
theorem Equation2499_implies_Equation3883 (G : Type*) [Magma G] (h : Equation2499 G) : Equation3883 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1 in 12
  have eq28 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2.1 in 9
  have eq36 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq23 -- superposition 23,9, 9 into 23, unify on (0).2 in 9 and (0).1.1 in 23
  have eq47 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq36 eq28 -- backward demodulation 28,36
  have eq48 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq36 eq27 -- backward demodulation 27,36
  have eq50 : sK0 ≠ (sK0 ◇ sK0) := superpose eq47 eq10 -- backward demodulation 10,47
  have eq58 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq48 eq12 -- superposition 12,48, 48 into 12, unify on (0).2 in 48 and (0).1.1 in 12
  have eq77 : sK0 ≠ sK0 := superpose eq58 eq50 -- superposition 50,58, 58 into 50, unify on (0).2 in 58 and (0).2 in 50
  subsumption eq77 rfl


@[equational_result]
theorem Equation2499_implies_Equation1041 (G : Type*) [Magma G] (h : Equation2499 G) : Equation1041 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1 in 12
  have eq28 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2.1 in 9
  have eq36 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq23 -- superposition 23,9, 9 into 23, unify on (0).2 in 9 and (0).1.1 in 23
  have eq47 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq36 eq28 -- backward demodulation 28,36
  have eq48 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq36 eq27 -- backward demodulation 27,36
  have eq50 : sK0 ≠ (sK0 ◇ sK0) := superpose eq47 eq10 -- backward demodulation 10,47
  have eq58 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq48 eq12 -- superposition 12,48, 48 into 12, unify on (0).2 in 48 and (0).1.1 in 12
  have eq77 : sK0 ≠ sK0 := superpose eq58 eq50 -- superposition 50,58, 58 into 50, unify on (0).2 in 58 and (0).2 in 50
  subsumption eq77 rfl


@[equational_result]
theorem Equation2499_implies_Equation3803 (G : Type*) [Magma G] (h : Equation2499 G) : Equation3803 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2.1 in 9
  have eq35 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq23 -- superposition 23,11, 11 into 23, unify on (0).2 in 11 and (0).1.1.2 in 23
  have eq36 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq23 -- superposition 23,9, 9 into 23, unify on (0).2 in 9 and (0).1.1 in 23
  have eq46 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq36 eq35 -- backward demodulation 35,36
  have eq47 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq36 eq26 -- backward demodulation 26,36
  have eq101 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq46 eq47 -- superposition 47,46, 46 into 47, unify on (0).2 in 46 and (0).1.1.2 in 47
  have eq246 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq101 eq10 -- superposition 10,101, 101 into 10, unify on (0).2 in 101 and (0).2 in 10
  subsumption eq246 rfl


@[equational_result]
theorem Equation2499_implies_Equation1904 (G : Type*) [Magma G] (h : Equation2499 G) : Equation1904 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1 in 12
  have eq28 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2.1 in 9
  have eq36 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq23 -- superposition 23,9, 9 into 23, unify on (0).2 in 9 and (0).1.1 in 23
  have eq47 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq36 eq28 -- backward demodulation 28,36
  have eq48 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq36 eq27 -- backward demodulation 27,36
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq48 eq12 -- superposition 12,48, 48 into 12, unify on (0).2 in 48 and (0).1.1 in 12
  have eq73 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) := superpose eq57 eq10 -- backward demodulation 10,57
  subsumption eq73 eq47


@[equational_result]
theorem Equation2499_implies_Equation2347 (G : Type*) [Magma G] (h : Equation2499 G) : Equation2347 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ X1) = ((X2 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq23 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1 in 12
  have eq35 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq23 -- superposition 23,11, 11 into 23, unify on (0).2 in 11 and (0).1.1.2 in 23
  have eq36 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq23 -- superposition 23,9, 9 into 23, unify on (0).2 in 9 and (0).1.1 in 23
  have eq46 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq36 eq35 -- backward demodulation 35,36
  have eq48 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq36 eq27 -- backward demodulation 27,36
  have eq49 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq36 eq20 -- backward demodulation 20,36
  have eq53 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq48 eq48 -- superposition 48,48, 48 into 48, unify on (0).2 in 48 and (0).1.1 in 48
  have eq62 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := superpose eq53 eq10 -- backward demodulation 10,53
  have eq99 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq46 eq49 -- superposition 49,46, 46 into 49, unify on (0).2 in 46 and (0).1 in 49
  have eq147 : sK0 ≠ sK0 := superpose eq99 eq62 -- superposition 62,99, 99 into 62, unify on (0).2 in 99 and (0).2 in 62
  subsumption eq147 rfl


@[equational_result]
theorem Equation2499_implies_Equation2381 (G : Type*) [Magma G] (h : Equation2499 G) : Equation2381 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ X1) = ((X2 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq23 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1 in 12
  have eq35 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq23 -- superposition 23,11, 11 into 23, unify on (0).2 in 11 and (0).1.1.2 in 23
  have eq36 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq23 -- superposition 23,9, 9 into 23, unify on (0).2 in 9 and (0).1.1 in 23
  have eq46 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq36 eq35 -- backward demodulation 35,36
  have eq48 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq36 eq27 -- backward demodulation 27,36
  have eq49 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq36 eq20 -- backward demodulation 20,36
  have eq50 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := superpose eq9 eq48 -- superposition 48,9, 9 into 48, unify on (0).2 in 9 and (0).1.1 in 48
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq48 eq12 -- superposition 12,48, 48 into 12, unify on (0).2 in 48 and (0).1.1 in 12
  have eq70 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq57 eq50 -- backward demodulation 50,57
  have eq73 : sK0 ≠ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq70 eq10 -- backward demodulation 10,70
  have eq99 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq46 eq49 -- superposition 49,46, 46 into 49, unify on (0).2 in 46 and (0).1 in 49
  have eq147 : sK0 ≠ sK0 := superpose eq99 eq73 -- superposition 73,99, 99 into 73, unify on (0).2 in 99 and (0).2 in 73
  subsumption eq147 rfl


@[equational_result]
theorem Equation2499_implies_Equation2415 (G : Type*) [Magma G] (h : Equation2499 G) : Equation2415 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ X1) = ((X2 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq23 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq35 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq23 -- superposition 23,11, 11 into 23, unify on (0).2 in 11 and (0).1.1.2 in 23
  have eq36 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq23 -- superposition 23,9, 9 into 23, unify on (0).2 in 9 and (0).1.1 in 23
  have eq46 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq36 eq35 -- backward demodulation 35,36
  have eq49 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq36 eq20 -- backward demodulation 20,36
  have eq99 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq46 eq49 -- superposition 49,46, 46 into 49, unify on (0).2 in 46 and (0).1 in 49
  have eq176 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X2 := superpose eq99 eq49 -- superposition 49,99, 99 into 49, unify on (0).2 in 99 and (0).1 in 49
  have eq341 : sK0 ≠ sK0 := superpose eq176 eq10 -- superposition 10,176, 176 into 10, unify on (0).2 in 176 and (0).2 in 10
  subsumption eq341 rfl


@[equational_result]
theorem Equation158_implies_Equation3096 (G : Type*) [Magma G] (h : Equation158 G) : Equation3096 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq19 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK2) ◇ sK2) ◇ sK3) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq38 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK3) := superpose eq22 eq19 -- backward demodulation 19,22
  subsumption eq38 eq22


@[equational_result]
theorem Equation158_implies_Equation3100 (G : Type*) [Magma G] (h : Equation158 G) : Equation3100 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK3) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq19 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK2) ◇ sK3) ◇ sK3) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq38 : sK0 ≠ ((sK0 ◇ sK3) ◇ sK3) := superpose eq22 eq19 -- backward demodulation 19,22
  subsumption eq38 eq22


@[equational_result]
theorem Equation158_implies_Equation2453 (G : Type*) [Magma G] (h : Equation158 G) : Equation2453 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq20 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq16 eq13 -- backward demodulation 13,16
  have eq23 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq36 (X0 : G) : sK0 ≠ ((sK0 ◇ X0) ◇ sK1) := superpose eq16 eq20 -- superposition 20,16, 16 into 20, unify on (0).2 in 16 and (0).2.1 in 20
  subsumption eq36 eq23


@[equational_result]
theorem Equation256_implies_Equation2680 (G : Type*) [Magma G] (h : Equation256 G) : Equation2680 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq33 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X2) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).2.1 in 11
  have eq38 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := superpose eq33 eq10 -- backward demodulation 10,33
  subsumption eq38 eq9


@[equational_result]
theorem Equation524_implies_Equation3921 (G : Type*) [Magma G] (h : Equation524 G) : Equation3921 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X2) = (X3 ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq18 (X0 : G) : (sK0 ◇ sK1) ≠ ((X0 ◇ (sK0 ◇ sK2)) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq18 eq15


@[equational_result]
theorem Equation524_implies_Equation608 (G : Type*) [Magma G] (h : Equation524 G) : Equation608 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X3 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq25 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X2)) = (X0 ◇ (X0 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq67 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq16 eq25 -- forward demodulation 25,16
  have eq68 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK4 ◇ sK0)))) := superpose eq67 eq10 -- backward demodulation 10,67
  have eq69 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := superpose eq67 eq68 -- forward demodulation 68,67
  subsumption eq69 eq16


@[equational_result]
theorem Equation524_implies_Equation4606 (G : Type*) [Magma G] (h : Equation524 G) : Equation4606 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X2) = (X3 ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq98 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq98 eq13


@[equational_result]
theorem Equation524_implies_Equation454 (G : Type*) [Magma G] (h : Equation524 G) : Equation454 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X3 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq25 (X0 : G) : sK0 ≠ (sK0 ◇ (sK1 ◇ (X0 ◇ (sK2 ◇ sK0)))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2.2 in 10
  have eq26 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X2)) = (X0 ◇ (X0 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq29 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X2)))) = (X0 ◇ (X0 ◇ (X4 ◇ (X1 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq32 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X0 ◇ (X4 ◇ (X1 ◇ X2)))) = (X0 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X2)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq68 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq16 eq26 -- forward demodulation 26,16
  have eq73 (X0 X1 X2 X4 : G) : (X0 ◇ (X0 ◇ (X4 ◇ (X1 ◇ X2)))) = X2 := superpose eq9 eq32 -- forward demodulation 32,9
  have eq74 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X2)))) = X2 := superpose eq73 eq29 -- backward demodulation 29,73
  have eq133 (X0 : G) : sK0 ≠ (sK0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := superpose eq12 eq25 -- superposition 25,12, 12 into 25, unify on (0).2 in 12 and (0).2.2 in 25
  have eq140 (X0 : G) : sK0 ≠ (sK0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := superpose eq68 eq133 -- forward demodulation 133,68
  subsumption eq140 eq74


@[equational_result]
theorem Equation228_implies_Equation2847 (G : Type*) [Magma G] (h : Equation228 G) : Equation2847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 : sK0 ≠ (sK0 ◇ sK0) := superpose eq8 eq9 -- forward demodulation 9,8
  have eq11 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq12 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq13 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq13 rfl


@[equational_result]
theorem Equation228_implies_Equation23 (G : Type*) [Magma G] (h : Equation228 G) : Equation23 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq11


@[equational_result]
theorem Equation228_implies_Equation4065 (G : Type*) [Magma G] (h : Equation228 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq12 -- forward demodulation 12,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation228_implies_Equation326 (G : Type*) [Magma G] (h : Equation228 G) : Equation326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 rfl


@[equational_result]
theorem Equation228_implies_Equation359 (G : Type*) [Magma G] (h : Equation228 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq11


@[equational_result]
theorem Equation228_implies_Equation3722 (G : Type*) [Magma G] (h : Equation228 G) : Equation3722 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq14 rfl


@[equational_result]
theorem Equation228_implies_Equation3862 (G : Type*) [Magma G] (h : Equation228 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 : sK0 ≠ (sK0 ◇ sK0) := superpose eq8 eq9 -- forward demodulation 9,8
  have eq11 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq12 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq13 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq13 rfl


@[equational_result]
theorem Equation228_implies_Equation4380 (G : Type*) [Magma G] (h : Equation228 G) : Equation4380 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 rfl


@[equational_result]
theorem Equation228_implies_Equation2035 (G : Type*) [Magma G] (h : Equation228 G) : Equation2035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq12 -- forward demodulation 12,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation228_implies_Equation255 (G : Type*) [Magma G] (h : Equation228 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq12 -- forward demodulation 12,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation228_implies_Equation47 (G : Type*) [Magma G] (h : Equation228 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq12 -- forward demodulation 12,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation228_implies_Equation307 (G : Type*) [Magma G] (h : Equation228 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq11


@[equational_result]
theorem Equation228_implies_Equation1832 (G : Type*) [Magma G] (h : Equation228 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq12 -- forward demodulation 12,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation228_implies_Equation4470 (G : Type*) [Magma G] (h : Equation228 G) : Equation4470 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq13 -- forward demodulation 13,12
  subsumption eq14 rfl


@[equational_result]
theorem Equation228_implies_Equation1045 (G : Type*) [Magma G] (h : Equation228 G) : Equation1045 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq11 : sK0 ≠ (sK0 ◇ sK0) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : sK0 ≠ sK0 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).2 in 11
  subsumption eq14 rfl


@[equational_result]
theorem Equation228_implies_Equation3715 (G : Type*) [Magma G] (h : Equation228 G) : Equation3715 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq13 -- forward demodulation 13,12
  subsumption eq14 rfl


@[equational_result]
theorem Equation228_implies_Equation411 (G : Type*) [Magma G] (h : Equation228 G) : Equation411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11


@[equational_result]
theorem Equation228_implies_Equation1020 (G : Type*) [Magma G] (h : Equation228 G) : Equation1020 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq10 : sK0 ≠ (sK0 ◇ sK0) := superpose eq8 eq9 -- forward demodulation 9,8
  have eq11 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq12 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq13 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq13 rfl


@[equational_result]
theorem Equation228_implies_Equation375 (G : Type*) [Magma G] (h : Equation228 G) : Equation375 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 rfl


@[equational_result]
theorem Equation228_implies_Equation3887 (G : Type*) [Magma G] (h : Equation228 G) : Equation3887 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq11 : sK0 ≠ (sK0 ◇ sK0) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : sK0 ≠ sK0 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).2 in 11
  subsumption eq14 rfl


@[equational_result]
theorem Equation228_implies_Equation2644 (G : Type*) [Magma G] (h : Equation228 G) : Equation2644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq12 -- forward demodulation 12,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation228_implies_Equation2743 (G : Type*) [Magma G] (h : Equation228 G) : Equation2743 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq9


@[equational_result]
theorem Equation228_implies_Equation2540 (G : Type*) [Magma G] (h : Equation228 G) : Equation2540 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq9


@[equational_result]
theorem Equation228_implies_Equation2238 (G : Type*) [Magma G] (h : Equation228 G) : Equation2238 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq8


@[equational_result]
theorem Equation228_implies_Equation1921 (G : Type*) [Magma G] (h : Equation228 G) : Equation1921 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq9


@[equational_result]
theorem Equation228_implies_Equation1426 (G : Type*) [Magma G] (h : Equation228 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq12 -- forward demodulation 12,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation228_implies_Equation1223 (G : Type*) [Magma G] (h : Equation228 G) : Equation1223 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11


@[equational_result]
theorem Equation228_implies_Equation817 (G : Type*) [Magma G] (h : Equation228 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq12 -- forward demodulation 12,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation228_implies_Equation614 (G : Type*) [Magma G] (h : Equation228 G) : Equation614 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11


@[equational_result]
theorem Equation228_implies_Equation151 (G : Type*) [Magma G] (h : Equation228 G) : Equation151 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq11


@[equational_result]
theorem Equation228_implies_Equation99 (G : Type*) [Magma G] (h : Equation228 G) : Equation99 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq12 -- forward demodulation 12,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation228_implies_Equation2327 (G : Type*) [Magma G] (h : Equation228 G) : Equation2327 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq9


@[equational_result]
theorem Equation228_implies_Equation2936 (G : Type*) [Magma G] (h : Equation228 G) : Equation2936 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 : sK0 ≠ (sK0 ◇ sK0) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : sK0 ≠ sK0 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).2 in 11
  subsumption eq14 rfl


@[equational_result]
theorem Equation228_implies_Equation8 (G : Type*) [Magma G] (h : Equation228 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq11


@[equational_result]
theorem Equation228_implies_Equation3 (G : Type*) [Magma G] (h : Equation228 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation2490_implies_Equation1440 (G : Type*) [Magma G] (h : Equation2490 G) : Equation1440 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq11 (X0 X2 X4 X5 : G) : ((X4 ◇ (X0 ◇ X5)) ◇ X2) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X5)) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq22 (X0 X2 X4 : G) : ((X0 ◇ X4) ◇ X2) = X0 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.1 in 9
  have eq23 (X0 : G) : sK0 ≠ ((sK0 ◇ sK0) ◇ X0) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq23 eq22


@[equational_result]
theorem Equation1646_implies_Equation1856 (G : Type*) [Magma G] (h : Equation1646 G) : Equation1856 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq30 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq43 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq30 eq30 -- superposition 30,30, 30 into 30, unify on (0).2 in 30 and (0).1.1 in 30
  have eq48 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK2 ◇ sK3)) := superpose eq43 eq10 -- backward demodulation 10,43
  subsumption eq48 eq30


@[equational_result]
theorem Equation445_implies_Equation1262 (G : Type*) [Magma G] (h : Equation445 G) : Equation1262 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq13


@[equational_result]
theorem Equation445_implies_Equation3716 (G : Type*) [Magma G] (h : Equation445 G) : Equation3716 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq13 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 : sK0 ≠ (sK0 ◇ sK1) := superpose eq13 eq17 -- forward demodulation 17,13
  subsumption eq18 eq13


@[equational_result]
theorem Equation445_implies_Equation4399 (G : Type*) [Magma G] (h : Equation445 G) : Equation4399 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 : sK0 ≠ (sK0 ◇ sK1) := superpose eq13 eq17 -- forward demodulation 17,13
  subsumption eq18 eq13


@[equational_result]
theorem Equation445_implies_Equation636 (G : Type*) [Magma G] (h : Equation445 G) : Equation636 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK2) ◇ sK1))) := mod_symm nh
  have eq13 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq13


