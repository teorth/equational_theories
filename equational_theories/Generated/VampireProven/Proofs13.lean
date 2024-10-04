import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation3358_implies_Equation4155 (G : Type*) [Magma G] (h : Equation3358 G) : Equation4155 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X3 ◇ (X3 ◇ (X2 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq13


@[equational_result]
theorem Equation3577_implies_Equation4150 (G : Type*) [Magma G] (h : Equation3577 G) : Equation4150 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X3) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK3) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ X4) ◇ X5) = (X5 ◇ (X4 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : (X7 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X8 ◇ X9))) = ((((X5 ◇ X6) ◇ X2) ◇ (X0 ◇ X1)) ◇ X7) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq25 (X0 X3 X4 X5 X6 : G) : (X6 ◇ (X3 ◇ X0)) = (((X4 ◇ X5) ◇ X0) ◇ X6) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq27 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : (((X7 ◇ X8) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X9) = (X9 ◇ ((X3 ◇ X4) ◇ (X2 ◇ (X5 ◇ X6)))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq32 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK3 ◇ (X0 ◇ X1))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  have eq39 (X2 X3 X4 X5 X6 X7 X8 X9 : G) : (X9 ◇ ((X3 ◇ X4) ◇ (X2 ◇ (X5 ◇ X6)))) = ((X2 ◇ (X7 ◇ X8)) ◇ X9) := superpose eq9 eq27 -- forward demodulation 27,9
  have eq54 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (((X4 ◇ X5) ◇ X3) ◇ X0) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1 in 25
  have eq77 (X0 X2 X3 X4 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK3 ◇ (((X3 ◇ X4) ◇ X2) ◇ X0))) := superpose eq25 eq32 -- superposition 32,25, 25 into 32, unify on (0).2 in 25 and (0).2.2.2 in 32
  have eq102 (X0 X3 X6 : G) : (X6 ◇ (X3 ◇ X0)) = (X0 ◇ X6) := superpose eq54 eq25 -- backward demodulation 25,54
  have eq104 (X0 X1 X2 X3 X4 X7 X8 X9 : G) : (X7 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X8 ◇ X9))) = ((X2 ◇ (X0 ◇ X1)) ◇ X7) := superpose eq54 eq18 -- backward demodulation 18,54
  have eq111 (X2 X3 X4 X6 X7 X8 X9 : G) : ((X2 ◇ (X7 ◇ X8)) ◇ X9) = (X9 ◇ ((X3 ◇ X4) ◇ (X6 ◇ X2))) := superpose eq102 eq39 -- backward demodulation 39,102
  have eq123 (X2 X3 X4 X7 X8 X9 : G) : ((X2 ◇ (X7 ◇ X8)) ◇ X9) = (X9 ◇ (X2 ◇ (X3 ◇ X4))) := superpose eq102 eq111 -- forward demodulation 111,102
  have eq124 (X2 X4 X7 X8 X9 : G) : ((X2 ◇ (X7 ◇ X8)) ◇ X9) = (X9 ◇ (X4 ◇ X2)) := superpose eq102 eq123 -- forward demodulation 123,102
  have eq125 (X2 X7 X8 X9 : G) : ((X2 ◇ (X7 ◇ X8)) ◇ X9) = (X2 ◇ X9) := superpose eq102 eq124 -- forward demodulation 124,102
  have eq126 (X2 X8 X9 : G) : (X2 ◇ X9) = ((X8 ◇ X2) ◇ X9) := superpose eq102 eq125 -- forward demodulation 125,102
  have eq139 (X1 X2 X3 X4 X7 X8 X9 : G) : (X7 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X8 ◇ X9))) = ((X1 ◇ X2) ◇ X7) := superpose eq102 eq104 -- forward demodulation 104,102
  have eq140 (X2 X3 X4 X7 X8 X9 : G) : (X7 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X8 ◇ X9))) = (X2 ◇ X7) := superpose eq126 eq139 -- forward demodulation 139,126
  have eq141 (X2 X3 X4 X7 X9 : G) : (X2 ◇ X7) = (X7 ◇ (X9 ◇ (X2 ◇ (X3 ◇ X4)))) := superpose eq102 eq140 -- forward demodulation 140,102
  have eq142 (X2 X3 X4 X7 X9 : G) : (X2 ◇ X7) = (X7 ◇ ((X3 ◇ X4) ◇ X9)) := superpose eq102 eq141 -- forward demodulation 141,102
  have eq143 (X2 X4 X7 X9 : G) : (X2 ◇ X7) = (X7 ◇ (X4 ◇ X9)) := superpose eq126 eq142 -- forward demodulation 142,126
  subsumption eq77 eq143


@[equational_result]
theorem Equation3577_implies_Equation4332 (G : Type*) [Magma G] (h : Equation3577 G) : Equation4332 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X3) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ X4) ◇ X5) = (X5 ◇ (X4 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : (X7 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X8 ◇ X9))) = ((((X5 ◇ X6) ◇ X2) ◇ (X0 ◇ X1)) ◇ X7) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq25 (X0 X3 X4 X5 X6 : G) : (X6 ◇ (X3 ◇ X0)) = (((X4 ◇ X5) ◇ X0) ◇ X6) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq27 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : (((X7 ◇ X8) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X9) = (X9 ◇ ((X3 ◇ X4) ◇ (X2 ◇ (X5 ◇ X6)))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq38 (X2 X3 X4 X5 X6 X7 X8 X9 : G) : (X9 ◇ ((X3 ◇ X4) ◇ (X2 ◇ (X5 ◇ X6)))) = ((X2 ◇ (X7 ◇ X8)) ◇ X9) := superpose eq9 eq27 -- forward demodulation 27,9
  have eq45 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (((X4 ◇ X5) ◇ X3) ◇ X0) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1 in 25
  have eq87 (X0 X3 X6 : G) : (X6 ◇ (X3 ◇ X0)) = (X0 ◇ X6) := superpose eq45 eq25 -- backward demodulation 25,45
  have eq89 (X0 X1 X2 X3 X4 X7 X8 X9 : G) : (X7 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X8 ◇ X9))) = ((X2 ◇ (X0 ◇ X1)) ◇ X7) := superpose eq45 eq18 -- backward demodulation 18,45
  have eq96 (X2 X3 X4 X6 X7 X8 X9 : G) : ((X2 ◇ (X7 ◇ X8)) ◇ X9) = (X9 ◇ ((X3 ◇ X4) ◇ (X6 ◇ X2))) := superpose eq87 eq38 -- backward demodulation 38,87
  have eq101 : (sK2 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK0) := superpose eq87 eq10 -- backward demodulation 10,87
  have eq108 (X2 X3 X4 X7 X8 X9 : G) : ((X2 ◇ (X7 ◇ X8)) ◇ X9) = (X9 ◇ (X2 ◇ (X3 ◇ X4))) := superpose eq87 eq96 -- forward demodulation 96,87
  have eq109 (X2 X4 X7 X8 X9 : G) : ((X2 ◇ (X7 ◇ X8)) ◇ X9) = (X9 ◇ (X4 ◇ X2)) := superpose eq87 eq108 -- forward demodulation 108,87
  have eq110 (X2 X7 X8 X9 : G) : ((X2 ◇ (X7 ◇ X8)) ◇ X9) = (X2 ◇ X9) := superpose eq87 eq109 -- forward demodulation 109,87
  have eq111 (X2 X8 X9 : G) : (X2 ◇ X9) = ((X8 ◇ X2) ◇ X9) := superpose eq87 eq110 -- forward demodulation 110,87
  have eq122 (X1 X2 X3 X4 X7 X8 X9 : G) : (X7 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X8 ◇ X9))) = ((X1 ◇ X2) ◇ X7) := superpose eq87 eq89 -- forward demodulation 89,87
  have eq123 (X2 X3 X4 X7 X8 X9 : G) : (X7 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X8 ◇ X9))) = (X2 ◇ X7) := superpose eq111 eq122 -- forward demodulation 122,111
  have eq124 (X2 X3 X4 X7 X9 : G) : (X2 ◇ X7) = (X7 ◇ (X9 ◇ (X2 ◇ (X3 ◇ X4)))) := superpose eq87 eq123 -- forward demodulation 123,87
  have eq125 (X2 X3 X4 X7 X9 : G) : (X2 ◇ X7) = (X7 ◇ ((X3 ◇ X4) ◇ X9)) := superpose eq87 eq124 -- forward demodulation 124,87
  have eq126 (X2 X4 X7 X9 : G) : (X2 ◇ X7) = (X7 ◇ (X4 ◇ X9)) := superpose eq111 eq125 -- forward demodulation 125,111
  have eq159 (X0 X3 X4 : G) : (X3 ◇ X0) = (X4 ◇ X0) := superpose eq126 eq126 -- superposition 126,126, 126 into 126, unify on (0).2 in 126 and (0).2 in 126
  have eq245 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X0) = (X4 ◇ (X1 ◇ X2)) := superpose eq126 eq159 -- superposition 159,126, 126 into 159, unify on (0).2 in 126 and (0).1 in 159
  have eq280 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq159 eq101 -- superposition 101,159, 159 into 101, unify on (0).2 in 159 and (0).1 in 101
  subsumption eq280 eq245


@[equational_result]
theorem Equation3577_implies_Equation4433 (G : Type*) [Magma G] (h : Equation3577 G) : Equation4433 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X3) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ X4) ◇ X5) = (X5 ◇ (X4 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : (X7 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X8 ◇ X9))) = ((((X5 ◇ X6) ◇ X2) ◇ (X0 ◇ X1)) ◇ X7) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq25 (X0 X3 X4 X5 X6 : G) : (X6 ◇ (X3 ◇ X0)) = (((X4 ◇ X5) ◇ X0) ◇ X6) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq27 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : (((X7 ◇ X8) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X9) = (X9 ◇ ((X3 ◇ X4) ◇ (X2 ◇ (X5 ◇ X6)))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq38 (X2 X3 X4 X5 X6 X7 X8 X9 : G) : (X9 ◇ ((X3 ◇ X4) ◇ (X2 ◇ (X5 ◇ X6)))) = ((X2 ◇ (X7 ◇ X8)) ◇ X9) := superpose eq9 eq27 -- forward demodulation 27,9
  have eq45 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (((X4 ◇ X5) ◇ X3) ◇ X0) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1 in 25
  have eq87 (X0 X3 X6 : G) : (X6 ◇ (X3 ◇ X0)) = (X0 ◇ X6) := superpose eq45 eq25 -- backward demodulation 25,45
  have eq89 (X0 X1 X2 X3 X4 X7 X8 X9 : G) : (X7 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X8 ◇ X9))) = ((X2 ◇ (X0 ◇ X1)) ◇ X7) := superpose eq45 eq18 -- backward demodulation 18,45
  have eq96 (X2 X3 X4 X6 X7 X8 X9 : G) : ((X2 ◇ (X7 ◇ X8)) ◇ X9) = (X9 ◇ ((X3 ◇ X4) ◇ (X6 ◇ X2))) := superpose eq87 eq38 -- backward demodulation 38,87
  have eq101 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq87 eq10 -- backward demodulation 10,87
  have eq108 (X2 X3 X4 X7 X8 X9 : G) : ((X2 ◇ (X7 ◇ X8)) ◇ X9) = (X9 ◇ (X2 ◇ (X3 ◇ X4))) := superpose eq87 eq96 -- forward demodulation 96,87
  have eq109 (X2 X4 X7 X8 X9 : G) : ((X2 ◇ (X7 ◇ X8)) ◇ X9) = (X9 ◇ (X4 ◇ X2)) := superpose eq87 eq108 -- forward demodulation 108,87
  have eq110 (X2 X7 X8 X9 : G) : ((X2 ◇ (X7 ◇ X8)) ◇ X9) = (X2 ◇ X9) := superpose eq87 eq109 -- forward demodulation 109,87
  have eq111 (X2 X8 X9 : G) : (X2 ◇ X9) = ((X8 ◇ X2) ◇ X9) := superpose eq87 eq110 -- forward demodulation 110,87
  have eq122 (X1 X2 X3 X4 X7 X8 X9 : G) : (X7 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X8 ◇ X9))) = ((X1 ◇ X2) ◇ X7) := superpose eq87 eq89 -- forward demodulation 89,87
  have eq123 (X2 X3 X4 X7 X8 X9 : G) : (X7 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X8 ◇ X9))) = (X2 ◇ X7) := superpose eq111 eq122 -- forward demodulation 122,111
  have eq124 (X2 X3 X4 X7 X9 : G) : (X2 ◇ X7) = (X7 ◇ (X9 ◇ (X2 ◇ (X3 ◇ X4)))) := superpose eq87 eq123 -- forward demodulation 123,87
  have eq125 (X2 X3 X4 X7 X9 : G) : (X2 ◇ X7) = (X7 ◇ ((X3 ◇ X4) ◇ X9)) := superpose eq87 eq124 -- forward demodulation 124,87
  have eq126 (X2 X4 X7 X9 : G) : (X2 ◇ X7) = (X7 ◇ (X4 ◇ X9)) := superpose eq111 eq125 -- forward demodulation 125,111
  have eq159 (X0 X3 X4 : G) : (X3 ◇ X0) = (X4 ◇ X0) := superpose eq126 eq126 -- superposition 126,126, 126 into 126, unify on (0).2 in 126 and (0).2 in 126
  have eq163 (X0 X1 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ X1)) := superpose eq126 eq101 -- superposition 101,126, 126 into 101, unify on (0).2 in 126 and (0).2 in 101
  have eq193 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X0) = (X4 ◇ (X1 ◇ X2)) := superpose eq126 eq159 -- superposition 159,126, 126 into 159, unify on (0).2 in 126 and (0).1 in 159
  have eq314 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ (X2 ◇ (X0 ◇ X1)) := superpose eq159 eq163 -- superposition 163,159, 159 into 163, unify on (0).2 in 159 and (0).2 in 163
  subsumption eq314 eq193


@[equational_result]
theorem Equation3577_implies_Equation3747 (G : Type*) [Magma G] (h : Equation3577 G) : Equation3747 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X3) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ (sK3 ◇ sK4)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ X4) ◇ X5) = (X5 ◇ (X4 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : (X7 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X8 ◇ X9))) = ((((X5 ◇ X6) ◇ X2) ◇ (X0 ◇ X1)) ◇ X7) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq25 (X0 X3 X4 X5 X6 : G) : (X6 ◇ (X3 ◇ X0)) = (((X4 ◇ X5) ◇ X0) ◇ X6) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq27 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : (((X7 ◇ X8) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X9) = (X9 ◇ ((X3 ◇ X4) ◇ (X2 ◇ (X5 ◇ X6)))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq28 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X3 ◇ X4) ◇ X0) = (((X5 ◇ X6) ◇ (X1 ◇ X2)) ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq38 (X2 X3 X4 X5 X6 X7 X8 X9 : G) : (X9 ◇ ((X3 ◇ X4) ◇ (X2 ◇ (X5 ◇ X6)))) = ((X2 ◇ (X7 ◇ X8)) ◇ X9) := superpose eq9 eq27 -- forward demodulation 27,9
  have eq45 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (((X4 ◇ X5) ◇ X3) ◇ X0) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1 in 25
  have eq87 (X0 X3 X6 : G) : (X6 ◇ (X3 ◇ X0)) = (X0 ◇ X6) := superpose eq45 eq25 -- backward demodulation 25,45
  have eq89 (X0 X1 X2 X3 X4 X7 X8 X9 : G) : (X7 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X8 ◇ X9))) = ((X2 ◇ (X0 ◇ X1)) ◇ X7) := superpose eq45 eq18 -- backward demodulation 18,45
  have eq96 (X2 X3 X4 X6 X7 X8 X9 : G) : ((X2 ◇ (X7 ◇ X8)) ◇ X9) = (X9 ◇ ((X3 ◇ X4) ◇ (X6 ◇ X2))) := superpose eq87 eq38 -- backward demodulation 38,87
  have eq100 (X0 X2 X3 X4 X5 X6 : G) : ((X3 ◇ X4) ◇ X0) = ((X2 ◇ (X5 ◇ X6)) ◇ X0) := superpose eq87 eq28 -- backward demodulation 28,87
  have eq107 (X2 X3 X4 X7 X8 X9 : G) : ((X2 ◇ (X7 ◇ X8)) ◇ X9) = (X9 ◇ (X2 ◇ (X3 ◇ X4))) := superpose eq87 eq96 -- forward demodulation 96,87
  have eq108 (X2 X4 X7 X8 X9 : G) : ((X2 ◇ (X7 ◇ X8)) ◇ X9) = (X9 ◇ (X4 ◇ X2)) := superpose eq87 eq107 -- forward demodulation 107,87
  have eq109 (X2 X7 X8 X9 : G) : ((X2 ◇ (X7 ◇ X8)) ◇ X9) = (X2 ◇ X9) := superpose eq87 eq108 -- forward demodulation 108,87
  have eq110 (X2 X8 X9 : G) : (X2 ◇ X9) = ((X8 ◇ X2) ◇ X9) := superpose eq87 eq109 -- forward demodulation 109,87
  have eq120 (X0 X2 X3 X4 X6 : G) : ((X3 ◇ X4) ◇ X0) = ((X6 ◇ X2) ◇ X0) := superpose eq87 eq100 -- forward demodulation 100,87
  have eq121 (X1 X2 X3 X4 X7 X8 X9 : G) : (X7 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X8 ◇ X9))) = ((X1 ◇ X2) ◇ X7) := superpose eq87 eq89 -- forward demodulation 89,87
  have eq122 (X2 X3 X4 X7 X8 X9 : G) : (X7 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X8 ◇ X9))) = (X2 ◇ X7) := superpose eq110 eq121 -- forward demodulation 121,110
  have eq123 (X2 X3 X4 X7 X9 : G) : (X2 ◇ X7) = (X7 ◇ (X9 ◇ (X2 ◇ (X3 ◇ X4)))) := superpose eq87 eq122 -- forward demodulation 122,87
  have eq124 (X2 X3 X4 X7 X9 : G) : (X2 ◇ X7) = (X7 ◇ ((X3 ◇ X4) ◇ X9)) := superpose eq87 eq123 -- forward demodulation 123,87
  have eq125 (X2 X4 X7 X9 : G) : (X2 ◇ X7) = (X7 ◇ (X4 ◇ X9)) := superpose eq110 eq124 -- forward demodulation 124,110
  have eq151 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ X0) = ((X1 ◇ X2) ◇ (X4 ◇ X5)) := superpose eq125 eq125 -- superposition 125,125, 125 into 125, unify on (0).2 in 125 and (0).1 in 125
  have eq222 (X0 X1 : G) : (sK0 ◇ sK1) ≠ ((X0 ◇ X1) ◇ (sK3 ◇ sK4)) := superpose eq120 eq10 -- superposition 10,120, 120 into 10, unify on (0).2 in 120 and (0).2 in 10
  subsumption eq222 eq151


@[equational_result]
theorem Equation3577_implies_Equation3344 (G : Type*) [Magma G] (h : Equation3577 G) : Equation3344 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X3) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ X4) ◇ X5) = (X5 ◇ (X4 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq25 (X0 X3 X4 X5 X6 : G) : (X6 ◇ (X3 ◇ X0)) = (((X4 ◇ X5) ◇ X0) ◇ X6) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq45 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (((X4 ◇ X5) ◇ X3) ◇ X0) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1 in 25
  have eq87 (X0 X3 X6 : G) : (X6 ◇ (X3 ◇ X0)) = (X0 ◇ X6) := superpose eq45 eq25 -- backward demodulation 25,45
  have eq101 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq87 eq10 -- backward demodulation 10,87
  subsumption eq101 eq87


@[equational_result]
theorem Equation4178_implies_Equation3588 (G : Type*) [Magma G] (h : Equation4178 G) : Equation3588 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (X3 ◇ (X2 ◇ X0)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq25 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq20 -- forward demodulation 20,9
  have eq26 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X3 ◇ (X0 ◇ X0)) := superpose eq25 eq18 -- backward demodulation 18,25
  have eq27 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq25 eq9 -- backward demodulation 9,25
  have eq29 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK2)) := superpose eq25 eq10 -- backward demodulation 10,25
  have eq30 (X0 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ (X2 ◇ X0)) := superpose eq13 eq26 -- forward demodulation 26,13
  have eq33 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK0) := superpose eq13 eq29 -- superposition 29,13, 13 into 29, unify on (0).2 in 13 and (0).2 in 29
  have eq60 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq27 eq25 -- superposition 25,27, 27 into 25, unify on (0).2 in 27 and (0).2 in 25
  have eq80 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq13 eq30 -- superposition 30,13, 13 into 30, unify on (0).2 in 13 and (0).2 in 30
  have eq149 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK2) := superpose eq60 eq33 -- superposition 33,60, 60 into 33, unify on (0).2 in 60 and (0).2 in 33
  subsumption eq149 eq80


@[equational_result]
theorem Equation4178_implies_Equation3309 (G : Type*) [Magma G] (h : Equation4178 G) : Equation3309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ (X0 ◇ X1)) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ X0) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq18 (X0 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq25 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq28 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq25 eq18 -- backward demodulation 18,25
  have eq58 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X2) := superpose eq28 eq25 -- superposition 25,28, 28 into 25, unify on (0).2 in 28 and (0).2 in 25
  have eq189 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq58 eq15 -- superposition 15,58, 58 into 15, unify on (0).2 in 58 and (0).1 in 15
  subsumption eq189 eq58


@[equational_result]
theorem Equation4178_implies_Equation3515 (G : Type*) [Magma G] (h : Equation4178 G) : Equation3515 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (X3 ◇ (X2 ◇ X0)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq18 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq23 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X3 ◇ (X0 ◇ X0)) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq27 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq23 eq10 -- backward demodulation 10,23
  have eq28 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X3 ◇ X0) := superpose eq13 eq24 -- forward demodulation 24,13
  subsumption eq27 eq28


@[equational_result]
theorem Equation4178_implies_Equation4100 (G : Type*) [Magma G] (h : Equation4178 G) : Equation4100 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ (X0 ◇ X1)) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ X0) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq17 (X0 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq24 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq20 -- forward demodulation 20,9
  have eq27 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq24 eq17 -- backward demodulation 17,24
  have eq28 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq24 eq10 -- backward demodulation 10,24
  subsumption eq28 eq27


@[equational_result]
theorem Equation4178_implies_Equation3555 (G : Type*) [Magma G] (h : Equation4178 G) : Equation3555 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq25 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq20 -- forward demodulation 20,9
  have eq27 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq25 eq9 -- backward demodulation 9,25
  have eq29 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq25 eq10 -- backward demodulation 10,25
  have eq59 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq27 eq25 -- superposition 25,27, 27 into 25, unify on (0).2 in 27 and (0).2 in 25
  have eq71 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq59 eq29 -- backward demodulation 29,59
  have eq97 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq13 eq71 -- superposition 71,13, 13 into 71, unify on (0).2 in 13 and (0).2 in 71
  subsumption eq97 eq59


@[equational_result]
theorem Equation4178_implies_Equation3712 (G : Type*) [Magma G] (h : Equation4178 G) : Equation3712 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq23 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq25 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ X0)) := superpose eq23 eq15 -- backward demodulation 15,23
  have eq28 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X0) ◇ X3) = (X3 ◇ X0) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq36 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq29 eq10 -- superposition 10,29, 29 into 10, unify on (0).2 in 29 and (0).2 in 10
  subsumption eq36 eq29


@[equational_result]
theorem Equation4178_implies_Equation3280 (G : Type*) [Magma G] (h : Equation4178 G) : Equation3280 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ (X0 ◇ X1)) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ X0) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq18 (X0 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq26 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq26 eq9 -- backward demodulation 9,26
  have eq29 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq26 eq18 -- backward demodulation 18,26
  have eq58 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq28 eq26 -- superposition 26,28, 28 into 26, unify on (0).2 in 28 and (0).2 in 26
  have eq59 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ X1) := superpose eq29 eq26 -- superposition 26,29, 29 into 26, unify on (0).2 in 29 and (0).2 in 26
  have eq70 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq58 eq15 -- backward demodulation 15,58
  have eq96 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq13 eq70 -- superposition 70,13, 13 into 70, unify on (0).2 in 13 and (0).2 in 70
  subsumption eq96 eq59


@[equational_result]
theorem Equation4178_implies_Equation372 (G : Type*) [Magma G] (h : Equation4178 G) : Equation372 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ (X0 ◇ X1)) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ X0) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq17 (X0 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq24 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq20 -- forward demodulation 20,9
  have eq26 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq24 eq9 -- backward demodulation 9,24
  have eq27 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq24 eq17 -- backward demodulation 17,24
  have eq33 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq13 eq26 -- superposition 26,13, 13 into 26, unify on (0).2 in 13 and (0).2 in 26
  have eq38 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X2) ◇ X0) := superpose eq24 eq33 -- forward demodulation 33,24
  have eq58 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X2) := superpose eq27 eq24 -- superposition 24,27, 27 into 24, unify on (0).2 in 27 and (0).2 in 24
  have eq117 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK1) := superpose eq38 eq10 -- superposition 10,38, 38 into 10, unify on (0).2 in 38 and (0).2 in 10
  have eq163 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq58 eq58 -- superposition 58,58, 58 into 58, unify on (0).2 in 58 and (0).1 in 58
  have eq195 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK2) := superpose eq58 eq117 -- superposition 117,58, 58 into 117, unify on (0).2 in 58 and (0).2 in 117
  subsumption eq195 eq163


@[equational_result]
theorem Equation4178_implies_Equation3529 (G : Type*) [Magma G] (h : Equation4178 G) : Equation3529 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (X3 ◇ (X2 ◇ X0)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq25 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq20 -- forward demodulation 20,9
  have eq26 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X3 ◇ (X0 ◇ X0)) := superpose eq25 eq18 -- backward demodulation 18,25
  have eq29 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK1)) := superpose eq25 eq10 -- backward demodulation 10,25
  have eq30 (X0 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ (X2 ◇ X0)) := superpose eq13 eq26 -- forward demodulation 26,13
  subsumption eq29 eq30


@[equational_result]
theorem Equation4178_implies_Equation4138 (G : Type*) [Magma G] (h : Equation4178 G) : Equation4138 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq19 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2 in 14
  have eq23 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq27 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq23 eq10 -- backward demodulation 10,23
  subsumption eq27 eq23


@[equational_result]
theorem Equation4178_implies_Equation3470 (G : Type*) [Magma G] (h : Equation4178 G) : Equation3470 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (X3 ◇ (X2 ◇ X0)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq25 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq20 -- forward demodulation 20,9
  have eq26 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X3 ◇ (X0 ◇ X0)) := superpose eq25 eq18 -- backward demodulation 18,25
  have eq29 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK3)) := superpose eq25 eq10 -- backward demodulation 10,25
  have eq30 (X0 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ (X2 ◇ X0)) := superpose eq13 eq26 -- forward demodulation 26,13
  have eq80 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq13 eq30 -- superposition 30,13, 13 into 30, unify on (0).2 in 13 and (0).2 in 30
  have eq92 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK3) := superpose eq30 eq29 -- superposition 29,30, 30 into 29, unify on (0).2 in 30 and (0).2 in 29
  subsumption eq92 eq80


@[equational_result]
theorem Equation4178_implies_Equation3676 (G : Type*) [Magma G] (h : Equation4178 G) : Equation3676 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ (X0 ◇ X1)) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ X0) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq17 (X0 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq22 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq25 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq20 -- forward demodulation 20,9
  have eq28 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq25 eq17 -- backward demodulation 17,25
  subsumption eq22 eq28


@[equational_result]
theorem Equation4178_implies_Equation3736 (G : Type*) [Magma G] (h : Equation4178 G) : Equation3736 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq22 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq25 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq20 -- forward demodulation 20,9
  subsumption eq22 eq25


@[equational_result]
theorem Equation4178_implies_Equation3279 (G : Type*) [Magma G] (h : Equation4178 G) : Equation3279 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ (X0 ◇ X1)) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ X0) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq18 (X0 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq26 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq26 eq9 -- backward demodulation 9,26
  have eq29 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq26 eq18 -- backward demodulation 18,26
  have eq58 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq28 eq26 -- superposition 26,28, 28 into 26, unify on (0).2 in 28 and (0).2 in 26
  have eq59 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X2) := superpose eq29 eq26 -- superposition 26,29, 29 into 26, unify on (0).2 in 29 and (0).2 in 26
  have eq70 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq58 eq15 -- backward demodulation 15,58
  have eq96 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq13 eq70 -- superposition 70,13, 13 into 70, unify on (0).2 in 13 and (0).2 in 70
  subsumption eq96 eq59


@[equational_result]
theorem Equation4178_implies_Equation4443 (G : Type*) [Magma G] (h : Equation4178 G) : Equation4443 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : ((sK1 ◇ sK0) ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq25 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq27 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq25 eq9 -- backward demodulation 9,25
  have eq58 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq27 eq25 -- superposition 25,27, 27 into 25, unify on (0).2 in 27 and (0).2 in 25
  have eq71 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq58 eq15 -- backward demodulation 15,58
  subsumption eq71 eq25


@[equational_result]
theorem Equation4178_implies_Equation3961 (G : Type*) [Magma G] (h : Equation4178 G) : Equation3961 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq25 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq27 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq25 eq9 -- backward demodulation 9,25
  have eq35 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq27 eq15 -- superposition 15,27, 27 into 15, unify on (0).2 in 27 and (0).2 in 15
  subsumption eq35 rfl


@[equational_result]
theorem Equation4178_implies_Equation3342 (G : Type*) [Magma G] (h : Equation4178 G) : Equation3342 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq25 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).2 in 15
  have eq26 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq26 eq9 -- backward demodulation 9,26
  have eq58 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq28 eq26 -- superposition 26,28, 28 into 26, unify on (0).2 in 28 and (0).2 in 26
  have eq96 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq58 eq25 -- superposition 25,58, 58 into 25, unify on (0).2 in 58 and (0).2 in 25
  subsumption eq96 rfl


@[equational_result]
theorem Equation4178_implies_Equation3274 (G : Type*) [Magma G] (h : Equation4178 G) : Equation3274 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ (X0 ◇ X1)) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK2)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ X0) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq18 (X0 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq25 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).2 in 15
  have eq26 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq26 eq9 -- backward demodulation 9,26
  have eq29 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq26 eq18 -- backward demodulation 18,26
  have eq58 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq28 eq26 -- superposition 26,28, 28 into 26, unify on (0).2 in 28 and (0).2 in 26
  have eq59 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X2) := superpose eq29 eq26 -- superposition 26,29, 29 into 26, unify on (0).2 in 29 and (0).2 in 26
  have eq88 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK1) := superpose eq58 eq25 -- superposition 25,58, 58 into 25, unify on (0).2 in 58 and (0).2 in 25
  subsumption eq88 eq59


@[equational_result]
theorem Equation4178_implies_Equation315 (G : Type*) [Magma G] (h : Equation4178 G) : Equation315 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ (X0 ◇ X1)) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ X0) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq17 (X0 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq25 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq20 -- forward demodulation 20,9
  have eq27 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq25 eq9 -- backward demodulation 9,25
  have eq28 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq25 eq17 -- backward demodulation 17,25
  have eq57 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq27 eq25 -- superposition 25,27, 27 into 25, unify on (0).2 in 27 and (0).2 in 25
  have eq58 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X2) := superpose eq28 eq25 -- superposition 25,28, 28 into 25, unify on (0).2 in 28 and (0).2 in 25
  have eq69 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq57 eq10 -- backward demodulation 10,57
  have eq73 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq13 eq69 -- superposition 69,13, 13 into 69, unify on (0).2 in 13 and (0).2 in 69
  subsumption eq73 eq58


@[equational_result]
theorem Equation4178_implies_Equation387 (G : Type*) [Magma G] (h : Equation4178 G) : Equation387 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq24 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq20 -- forward demodulation 20,9
  have eq26 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq24 eq9 -- backward demodulation 9,24
  have eq34 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq34 rfl


@[equational_result]
theorem Equation4178_implies_Equation4626 (G : Type*) [Magma G] (h : Equation4178 G) : Equation4626 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ (X0 ◇ X1)) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ X0) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq17 (X0 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq24 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq20 -- forward demodulation 20,9
  have eq27 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq24 eq17 -- backward demodulation 17,24
  have eq28 : ((sK2 ◇ sK3) ◇ sK2) ≠ (sK0 ◇ sK1) := superpose eq24 eq10 -- backward demodulation 10,24
  have eq46 : (sK2 ◇ sK3) ≠ (sK0 ◇ sK1) := superpose eq27 eq28 -- superposition 28,27, 27 into 28, unify on (0).2 in 27 and (0).1 in 28
  have eq59 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X2) := superpose eq27 eq24 -- superposition 24,27, 27 into 24, unify on (0).2 in 27 and (0).2 in 24
  have eq162 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq59 eq59 -- superposition 59,59, 59 into 59, unify on (0).2 in 59 and (0).1 in 59
  have eq190 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK2) := superpose eq59 eq46 -- superposition 46,59, 59 into 46, unify on (0).2 in 59 and (0).1 in 46
  subsumption eq190 eq162


@[equational_result]
theorem Equation4178_implies_Equation3301 (G : Type*) [Magma G] (h : Equation4178 G) : Equation3301 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ (X0 ◇ X1)) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ sK3)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ X0) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq18 (X0 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq26 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq29 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq26 eq18 -- backward demodulation 18,26
  have eq59 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X2) := superpose eq29 eq26 -- superposition 26,29, 29 into 26, unify on (0).2 in 29 and (0).2 in 26
  have eq159 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq59 eq59 -- superposition 59,59, 59 into 59, unify on (0).2 in 59 and (0).1 in 59
  have eq191 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK1) := superpose eq59 eq15 -- superposition 15,59, 59 into 15, unify on (0).2 in 59 and (0).2 in 15
  subsumption eq191 eq159


@[equational_result]
theorem Equation4178_implies_Equation4614 (G : Type*) [Magma G] (h : Equation4178 G) : Equation4614 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ (X0 ◇ X1)) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ X0) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq17 (X0 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq24 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq20 -- forward demodulation 20,9
  have eq27 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq24 eq17 -- backward demodulation 17,24
  have eq28 : ((sK2 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ sK1) := superpose eq24 eq10 -- backward demodulation 10,24
  have eq30 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK1) := superpose eq27 eq28 -- forward demodulation 28,27
  have eq59 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X2) := superpose eq27 eq24 -- superposition 24,27, 27 into 24, unify on (0).2 in 27 and (0).2 in 24
  have eq190 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq59 eq30 -- superposition 30,59, 59 into 30, unify on (0).2 in 59 and (0).2 in 30
  subsumption eq190 eq59


@[equational_result]
theorem Equation4178_implies_Equation4081 (G : Type*) [Magma G] (h : Equation4178 G) : Equation4081 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ (X0 ◇ X1)) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ X0) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq17 (X0 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq24 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq20 -- forward demodulation 20,9
  have eq26 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq24 eq9 -- backward demodulation 9,24
  have eq27 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq24 eq17 -- backward demodulation 17,24
  have eq28 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq24 eq10 -- backward demodulation 10,24
  have eq58 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq26 eq24 -- superposition 24,26, 26 into 24, unify on (0).2 in 26 and (0).2 in 24
  have eq59 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X2) := superpose eq27 eq24 -- superposition 24,27, 27 into 24, unify on (0).2 in 27 and (0).2 in 24
  have eq71 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq58 eq28 -- backward demodulation 28,58
  have eq75 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK1) := superpose eq24 eq71 -- superposition 71,24, 24 into 71, unify on (0).2 in 24 and (0).2 in 71
  subsumption eq75 eq59


@[equational_result]
theorem Equation4178_implies_Equation3270 (G : Type*) [Magma G] (h : Equation4178 G) : Equation3270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ (X0 ◇ X1)) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ X0) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq18 (X0 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq25 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).2 in 15
  have eq26 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq26 eq9 -- backward demodulation 9,26
  have eq29 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq26 eq18 -- backward demodulation 18,26
  have eq58 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq28 eq26 -- superposition 26,28, 28 into 26, unify on (0).2 in 28 and (0).2 in 26
  have eq59 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ X1) := superpose eq29 eq26 -- superposition 26,29, 29 into 26, unify on (0).2 in 29 and (0).2 in 26
  have eq88 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK1) := superpose eq58 eq25 -- superposition 25,58, 58 into 25, unify on (0).2 in 58 and (0).2 in 25
  subsumption eq88 eq59


@[equational_result]
theorem Equation4178_implies_Equation4105 (G : Type*) [Magma G] (h : Equation4178 G) : Equation4105 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ (X0 ◇ X1)) := superpose eq14 eq11 -- backward demodulation 11,14
  have eq16 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ X0) := superpose eq14 eq15 -- forward demodulation 15,14
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq14 eq16 -- forward demodulation 16,14
  have eq18 (X0 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq14 eq17 -- forward demodulation 17,14
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2 in 14
  have eq25 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq28 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq25 eq18 -- backward demodulation 18,25
  have eq29 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ sK1) := superpose eq25 eq10 -- backward demodulation 10,25
  have eq61 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X2) := superpose eq28 eq25 -- superposition 25,28, 28 into 25, unify on (0).2 in 28 and (0).2 in 25
  have eq133 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq61 eq61 -- superposition 61,61, 61 into 61, unify on (0).2 in 61 and (0).1 in 61
  have eq149 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ sK1) ◇ sK1) := superpose eq61 eq29 -- superposition 29,61, 61 into 29, unify on (0).2 in 61 and (0).2.1 in 29
  subsumption eq149 eq133


@[equational_result]
theorem Equation4178_implies_Equation3696 (G : Type*) [Magma G] (h : Equation4178 G) : Equation3696 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ (X0 ◇ X1)) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ X0) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq17 (X0 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq21 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq25 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq20 -- forward demodulation 20,9
  have eq28 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq25 eq17 -- backward demodulation 17,25
  have eq61 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ X1) := superpose eq28 eq25 -- superposition 25,28, 28 into 25, unify on (0).2 in 28 and (0).2 in 25
  have eq70 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq25 eq21 -- superposition 21,25, 25 into 21, unify on (0).2 in 25 and (0).2 in 21
  subsumption eq70 eq61


@[equational_result]
theorem Equation4178_implies_Equation38 (G : Type*) [Magma G] (h : Equation4178 G) : Equation38 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq22 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ X0)) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq27 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X0) ◇ X3) = (X3 ◇ X0) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq28 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq22 eq27 -- forward demodulation 27,22
  have eq43 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ X1) := superpose eq28 eq22 -- superposition 22,28, 28 into 22, unify on (0).2 in 28 and (0).2 in 22
  have eq75 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq43 eq43 -- superposition 43,43, 43 into 43, unify on (0).2 in 43 and (0).1 in 43
  have eq93 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq43 eq10 -- superposition 10,43, 43 into 10, unify on (0).2 in 43 and (0).1 in 10
  subsumption eq93 eq75


@[equational_result]
theorem Equation4178_implies_Equation3583 (G : Type*) [Magma G] (h : Equation4178 G) : Equation3583 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (X3 ◇ (X2 ◇ X0)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.2 in 13
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq25 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq20 -- forward demodulation 20,9
  have eq26 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X3 ◇ (X0 ◇ X0)) := superpose eq25 eq18 -- backward demodulation 18,25
  have eq27 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq25 eq9 -- backward demodulation 9,25
  have eq29 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK1)) := superpose eq25 eq10 -- backward demodulation 10,25
  have eq30 (X0 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ (X2 ◇ X0)) := superpose eq13 eq26 -- forward demodulation 26,13
  have eq33 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK0) := superpose eq13 eq29 -- superposition 29,13, 13 into 29, unify on (0).2 in 13 and (0).2 in 29
  have eq60 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq27 eq25 -- superposition 25,27, 27 into 25, unify on (0).2 in 27 and (0).2 in 25
  have eq80 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq13 eq30 -- superposition 30,13, 13 into 30, unify on (0).2 in 13 and (0).2 in 30
  have eq149 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK2) := superpose eq60 eq33 -- superposition 33,60, 60 into 33, unify on (0).2 in 60 and (0).2 in 33
  subsumption eq149 eq80


@[equational_result]
theorem Equation4178_implies_Equation4605 (G : Type*) [Magma G] (h : Equation4178 G) : Equation4605 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ (X0 ◇ X1)) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ X0) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq17 (X0 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq24 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq20 -- forward demodulation 20,9
  have eq27 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq24 eq17 -- backward demodulation 17,24
  have eq28 : ((sK1 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ sK1) := superpose eq24 eq10 -- backward demodulation 10,24
  have eq30 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK1) := superpose eq27 eq28 -- forward demodulation 28,27
  have eq59 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X2) := superpose eq27 eq24 -- superposition 24,27, 27 into 24, unify on (0).2 in 27 and (0).2 in 24
  have eq190 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq59 eq30 -- superposition 30,59, 59 into 30, unify on (0).2 in 59 and (0).2 in 30
  subsumption eq190 eq59


@[equational_result]
theorem Equation4178_implies_Equation4195 (G : Type*) [Magma G] (h : Equation4178 G) : Equation4195 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ (X0 ◇ X1)) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ X0) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq17 (X0 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq24 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq20 -- forward demodulation 20,9
  have eq27 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq24 eq17 -- backward demodulation 17,24
  have eq28 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ sK0) := superpose eq24 eq10 -- backward demodulation 10,24
  subsumption eq28 eq27


@[equational_result]
theorem Equation4178_implies_Equation3273 (G : Type*) [Magma G] (h : Equation4178 G) : Equation3273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ (X0 ◇ X1)) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ X0) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq18 (X0 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq25 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).2 in 15
  have eq26 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq21 -- forward demodulation 21,9
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq26 eq9 -- backward demodulation 9,26
  have eq29 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq26 eq18 -- backward demodulation 18,26
  have eq58 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq28 eq26 -- superposition 26,28, 28 into 26, unify on (0).2 in 28 and (0).2 in 26
  have eq59 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X2) := superpose eq29 eq26 -- superposition 26,29, 29 into 26, unify on (0).2 in 29 and (0).2 in 26
  have eq88 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK1) := superpose eq58 eq25 -- superposition 25,58, 58 into 25, unify on (0).2 in 58 and (0).2 in 25
  subsumption eq88 eq59


@[equational_result]
theorem Equation3561_implies_Equation3537 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3537 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq52 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ X0) ◇ X3)) := superpose eq28 eq11 -- superposition 11,28, 28 into 11, unify on (0).2 in 28 and (0).2.2.1 in 11
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq101 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X1 ◇ ((X1 ◇ X0) ◇ X3)) := superpose eq94 eq52 -- backward demodulation 52,94
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq126 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK1)) := superpose eq108 eq10 -- backward demodulation 10,108
  have eq150 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq116 eq101 -- forward demodulation 101,116
  have eq151 (X1 X2 X3 : G) : (X3 ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq116 eq150 -- forward demodulation 150,116
  have eq152 (X1 X2 X3 : G) : (X3 ◇ X1) = (X3 ◇ (X2 ◇ X1)) := superpose eq108 eq151 -- forward demodulation 151,108
  have eq178 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq180 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq178 -- forward demodulation 178,108
  have eq183 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq116 eq180 -- superposition 180,116, 116 into 180, unify on (0).2 in 116 and (0).1 in 180
  have eq202 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq183 eq126 -- superposition 126,183, 183 into 126, unify on (0).2 in 183 and (0).2.2 in 126
  subsumption eq202 eq152


@[equational_result]
theorem Equation3561_implies_Equation3973 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3973 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq9 eq29 -- forward demodulation 29,9
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq98 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq94 eq24 -- backward demodulation 24,94
  have eq106 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) := superpose eq95 eq35 -- backward demodulation 35,95
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq123 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq108 eq106 -- backward demodulation 106,108
  have eq132 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq116 eq10 -- backward demodulation 10,116
  have eq143 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X2 ◇ (X0 ◇ X4)) := superpose eq116 eq98 -- forward demodulation 98,116
  have eq144 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X4 ◇ X2) := superpose eq116 eq143 -- forward demodulation 143,116
  have eq145 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = (X4 ◇ X2) := superpose eq116 eq144 -- forward demodulation 144,116
  have eq146 (X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X1 ◇ X2) ◇ (X3 ◇ X4)) := superpose eq108 eq145 -- forward demodulation 145,108
  have eq178 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq179 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq178 -- forward demodulation 178,108
  have eq182 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq116 eq179 -- superposition 179,116, 116 into 179, unify on (0).2 in 116 and (0).1 in 179
  have eq186 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (X3 ◇ (X1 ◇ X2)) := superpose eq179 eq182 -- superposition 182,179, 179 into 182, unify on (0).2 in 179 and (0).1 in 182
  have eq249 (X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ X3) := superpose eq123 eq146 -- superposition 146,123, 123 into 146, unify on (0).2 in 123 and (0).2 in 146
  have eq279 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK1)) := superpose eq249 eq132 -- superposition 132,249, 249 into 132, unify on (0).2 in 249 and (0).2 in 132
  subsumption eq279 eq186


@[equational_result]
theorem Equation3561_implies_Equation3675 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3675 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq177 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq179 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq177 -- forward demodulation 177,108
  have eq186 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq179 eq10 -- superposition 10,179, 179 into 10, unify on (0).2 in 179 and (0).2 in 10
  subsumption eq186 eq116


@[equational_result]
theorem Equation3561_implies_Equation3994 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3994 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq9 eq29 -- forward demodulation 29,9
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq98 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq94 eq24 -- backward demodulation 24,94
  have eq106 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) := superpose eq95 eq35 -- backward demodulation 35,95
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq123 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq108 eq106 -- backward demodulation 106,108
  have eq132 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK2) ◇ sK2) := superpose eq116 eq10 -- backward demodulation 10,116
  have eq143 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X2 ◇ (X0 ◇ X4)) := superpose eq116 eq98 -- forward demodulation 98,116
  have eq144 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X4 ◇ X2) := superpose eq116 eq143 -- forward demodulation 143,116
  have eq145 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = (X4 ◇ X2) := superpose eq116 eq144 -- forward demodulation 144,116
  have eq146 (X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X1 ◇ X2) ◇ (X3 ◇ X4)) := superpose eq108 eq145 -- forward demodulation 145,108
  have eq178 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq179 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq178 -- forward demodulation 178,108
  have eq182 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq116 eq179 -- superposition 179,116, 116 into 179, unify on (0).2 in 116 and (0).1 in 179
  have eq195 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK2) := superpose eq182 eq132 -- superposition 132,182, 182 into 132, unify on (0).2 in 182 and (0).2 in 132
  have eq249 (X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ X3) := superpose eq123 eq146 -- superposition 146,123, 123 into 146, unify on (0).2 in 123 and (0).2 in 146
  have eq269 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X1) := superpose eq182 eq249 -- superposition 249,182, 182 into 249, unify on (0).2 in 182 and (0).1 in 249
  have eq322 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq269 eq269 -- superposition 269,269, 269 into 269, unify on (0).2 in 269 and (0).1 in 269
  have eq354 (X0 X1 : G) : (X1 ◇ sK2) ≠ (X0 ◇ sK0) := superpose eq269 eq195 -- superposition 195,269, 269 into 195, unify on (0).2 in 269 and (0).1 in 195
  subsumption eq354 eq322


@[equational_result]
theorem Equation3561_implies_Equation4537 (G : Type*) [Magma G] (h : Equation3561 G) : Equation4537 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq9 eq29 -- forward demodulation 29,9
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq51 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq51 -- backward demodulation 51,94
  have eq98 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq94 eq24 -- backward demodulation 24,94
  have eq106 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) := superpose eq95 eq35 -- backward demodulation 35,95
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq123 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq108 eq106 -- backward demodulation 106,108
  have eq126 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ sK2) := superpose eq108 eq10 -- backward demodulation 10,108
  have eq141 : (sK3 ◇ sK2) ≠ (sK2 ◇ sK0) := superpose eq116 eq126 -- forward demodulation 126,116
  have eq144 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X2 ◇ (X0 ◇ X4)) := superpose eq116 eq98 -- forward demodulation 98,116
  have eq145 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X4 ◇ X2) := superpose eq116 eq144 -- forward demodulation 144,116
  have eq146 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = (X4 ◇ X2) := superpose eq116 eq145 -- forward demodulation 145,116
  have eq147 (X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X1 ◇ X2) ◇ (X3 ◇ X4)) := superpose eq108 eq146 -- forward demodulation 146,108
  have eq179 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq180 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq179 -- forward demodulation 179,108
  have eq183 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq116 eq180 -- superposition 180,116, 116 into 180, unify on (0).2 in 116 and (0).1 in 180
  have eq248 (X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ X1) := superpose eq123 eq147 -- superposition 147,123, 123 into 147, unify on (0).2 in 123 and (0).2 in 147
  have eq265 : (sK3 ◇ sK2) ≠ (sK0 ◇ sK2) := superpose eq248 eq141 -- backward demodulation 141,248
  subsumption eq265 eq183


@[equational_result]
theorem Equation3561_implies_Equation363 (G : Type*) [Magma G] (h : Equation3561 G) : Equation363 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq9 eq29 -- forward demodulation 29,9
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq51 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq51 -- backward demodulation 51,94
  have eq98 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq94 eq24 -- backward demodulation 24,94
  have eq106 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) := superpose eq95 eq35 -- backward demodulation 35,95
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq123 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq108 eq106 -- backward demodulation 106,108
  have eq142 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X2 ◇ (X0 ◇ X4)) := superpose eq116 eq98 -- forward demodulation 98,116
  have eq143 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X4 ◇ X2) := superpose eq116 eq142 -- forward demodulation 142,116
  have eq144 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = (X4 ◇ X2) := superpose eq116 eq143 -- forward demodulation 143,116
  have eq145 (X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X1 ◇ X2) ◇ (X3 ◇ X4)) := superpose eq108 eq144 -- forward demodulation 144,108
  have eq177 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq178 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq177 -- forward demodulation 177,108
  have eq181 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq116 eq178 -- superposition 178,116, 116 into 178, unify on (0).2 in 116 and (0).1 in 178
  have eq185 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (X3 ◇ (X1 ◇ X2)) := superpose eq178 eq181 -- superposition 181,178, 178 into 181, unify on (0).2 in 178 and (0).1 in 181
  have eq244 (X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ X3) := superpose eq123 eq145 -- superposition 145,123, 123 into 145, unify on (0).2 in 123 and (0).2 in 145
  have eq276 : (sK0 ◇ sK0) ≠ (sK2 ◇ (sK0 ◇ sK1)) := superpose eq244 eq10 -- superposition 10,244, 244 into 10, unify on (0).2 in 244 and (0).2 in 10
  subsumption eq276 eq185


@[equational_result]
theorem Equation3561_implies_Equation3740 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3740 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq177 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq178 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK2)) := superpose eq116 eq10 -- superposition 10,116, 116 into 10, unify on (0).2 in 116 and (0).2 in 10
  have eq179 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq177 -- forward demodulation 177,108
  subsumption eq178 eq179


@[equational_result]
theorem Equation3561_implies_Equation3474 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3474 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq25 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq28 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq29 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq35 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq9 eq28 -- forward demodulation 28,9
  have eq37 (X0 X2 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X0)))) := superpose eq9 eq29 -- superposition 29,9, 9 into 29, unify on (0).2 in 9 and (0).2.2.2.2 in 29
  have eq47 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq29 eq29 -- superposition 29,29, 29 into 29, unify on (0).2 in 29 and (0).2.2 in 29
  have eq48 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq9 eq29 -- superposition 29,9, 9 into 29, unify on (0).2 in 9 and (0).2 in 29
  have eq57 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq29 eq9 -- superposition 9,29, 29 into 9, unify on (0).2 in 29 and (0).2.2 in 9
  have eq62 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X0) ◇ X0) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq65 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq47 -- superposition 47,9, 9 into 47, unify on (0).2 in 9 and (0).2.2 in 47
  have eq66 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2.2 in 47
  have eq68 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq47 eq47 -- superposition 47,47, 47 into 47, unify on (0).2 in 47 and (0).2.2 in 47
  have eq70 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq29 eq47 -- superposition 47,29, 29 into 47, unify on (0).2 in 29 and (0).2 in 47
  have eq79 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq47 eq11 -- superposition 11,47, 47 into 11, unify on (0).2 in 47 and (0).2.2 in 11
  have eq80 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq47 eq9 -- superposition 9,47, 47 into 9, unify on (0).2 in 47 and (0).2.2 in 9
  have eq85 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := superpose eq68 eq10 -- backward demodulation 10,68
  have eq86 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq47 eq70 -- forward demodulation 70,47
  have eq87 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq86 eq62 -- backward demodulation 62,86
  have eq89 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq87 eq68 -- backward demodulation 68,87
  have eq90 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq89 eq65 -- backward demodulation 65,89
  have eq91 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq89 eq66 -- backward demodulation 66,89
  have eq96 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq89 eq85 -- backward demodulation 85,89
  have eq99 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ X1) := superpose eq91 eq79 -- forward demodulation 79,91
  have eq101 (X0 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ X0)) := superpose eq99 eq37 -- backward demodulation 37,99
  have eq104 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq90 eq80 -- forward demodulation 80,90
  have eq106 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X1))) = ((X2 ◇ X2) ◇ X0) := superpose eq104 eq57 -- backward demodulation 57,104
  have eq107 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) := superpose eq104 eq12 -- backward demodulation 12,104
  have eq110 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq104 eq25 -- backward demodulation 25,104
  have eq113 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq104 eq35 -- backward demodulation 35,104
  have eq131 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq87 eq9 -- superposition 9,87, 87 into 9, unify on (0).2 in 87 and (0).2.2.1 in 9
  have eq141 (X0 X1 X2 X4 : G) : (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq107 eq107 -- superposition 107,107, 107 into 107, unify on (0).2 in 107 and (0).2.1.1 in 107
  have eq153 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq101 eq101 -- superposition 101,101, 101 into 101, unify on (0).2 in 101 and (0).2.2 in 101
  have eq168 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq89 eq153 -- forward demodulation 153,89
  have eq169 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose eq101 eq168 -- forward demodulation 168,101
  have eq170 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq169 eq106 -- backward demodulation 106,169
  have eq171 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq169 eq110 -- backward demodulation 110,169
  have eq174 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq169 eq131 -- backward demodulation 131,169
  have eq177 (X0 X1 X2 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq169 eq141 -- backward demodulation 141,169
  have eq178 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := superpose eq169 eq113 -- backward demodulation 113,169
  have eq179 (X0 X1 X2 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq170 eq171 -- forward demodulation 171,170
  have eq182 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq47 eq178 -- forward demodulation 178,47
  have eq201 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := superpose eq101 eq182 -- superposition 182,101, 101 into 182, unify on (0).2 in 101 and (0).2.1 in 182
  have eq205 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X2 ◇ X0)) := superpose eq9 eq182 -- superposition 182,9, 9 into 182, unify on (0).2 in 9 and (0).2.2 in 182
  have eq208 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) := superpose eq101 eq182 -- superposition 182,101, 101 into 182, unify on (0).2 in 101 and (0).2.2 in 182
  have eq234 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq169 eq201 -- forward demodulation 201,169
  have eq235 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq234 eq177 -- backward demodulation 177,234
  have eq238 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ X2) = (X4 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq235 eq179 -- backward demodulation 179,235
  have eq246 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X2 ◇ X0)) := superpose eq238 eq205 -- forward demodulation 205,238
  have eq248 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X1)) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq169 eq208 -- forward demodulation 208,169
  have eq249 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq101 eq248 -- forward demodulation 248,101
  have eq250 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq249 eq174 -- backward demodulation 174,249
  have eq261 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ X0) := superpose eq250 eq246 -- backward demodulation 246,250
  have eq265 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ (X3 ◇ X2)) := superpose eq261 eq11 -- backward demodulation 11,261
  have eq295 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq47 eq265 -- superposition 265,47, 47 into 265, unify on (0).2 in 47 and (0).2 in 265
  have eq448 (X0 : G) : (X0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ sK0)) := superpose eq295 eq96 -- superposition 96,295, 295 into 96, unify on (0).2 in 295 and (0).1 in 96
  subsumption eq448 eq250


@[equational_result]
theorem Equation3561_implies_Equation3600 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3600 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq126 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK1)) := superpose eq108 eq10 -- backward demodulation 10,108
  have eq177 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq179 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq177 -- forward demodulation 177,108
  have eq182 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq116 eq179 -- superposition 179,116, 116 into 179, unify on (0).2 in 116 and (0).1 in 179
  have eq187 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (X3 ◇ (X1 ◇ X2)) := superpose eq179 eq182 -- superposition 182,179, 179 into 182, unify on (0).2 in 179 and (0).1 in 182
  have eq199 (X0 : G) : (X0 ◇ sK1) ≠ (sK2 ◇ (X0 ◇ sK1)) := superpose eq182 eq126 -- superposition 126,182, 182 into 126, unify on (0).2 in 182 and (0).1 in 126
  subsumption eq199 eq187


@[equational_result]
theorem Equation3561_implies_Equation3790 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3790 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq178 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq116 eq10 -- superposition 10,116, 116 into 10, unify on (0).2 in 116 and (0).2 in 10
  subsumption eq178 eq116


@[equational_result]
theorem Equation3561_implies_Equation3491 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3491 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq30 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq30 eq30 -- superposition 30,30, 30 into 30, unify on (0).2 in 30 and (0).2.2 in 30
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq30 eq9 -- superposition 9,30, 30 into 9, unify on (0).2 in 30 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq126 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq108 eq10 -- backward demodulation 10,108
  have eq175 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq177 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq175 -- forward demodulation 175,108
  have eq180 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq116 eq177 -- superposition 177,116, 116 into 177, unify on (0).2 in 116 and (0).1 in 177
  have eq185 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (X3 ◇ (X1 ◇ X2)) := superpose eq177 eq180 -- superposition 180,177, 177 into 180, unify on (0).2 in 177 and (0).1 in 180
  have eq193 (X0 : G) : (X0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ sK0)) := superpose eq180 eq126 -- superposition 126,180, 180 into 126, unify on (0).2 in 180 and (0).1 in 126
  subsumption eq193 eq185


@[equational_result]
theorem Equation3561_implies_Equation3695 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3695 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq177 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq179 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq177 -- forward demodulation 177,108
  have eq183 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq116 eq179 -- superposition 179,116, 116 into 179, unify on (0).2 in 116 and (0).1 in 179
  have eq189 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (X3 ◇ (X1 ◇ X2)) := superpose eq179 eq183 -- superposition 183,179, 179 into 183, unify on (0).2 in 179 and (0).1 in 183
  have eq201 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq183 eq10 -- superposition 10,183, 183 into 10, unify on (0).2 in 183 and (0).2 in 10
  subsumption eq201 eq189


@[equational_result]
theorem Equation3561_implies_Equation3483 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3483 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq25 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq28 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq29 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq32 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2.1 in 9
  have eq35 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq9 eq28 -- forward demodulation 28,9
  have eq37 (X0 X2 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X0)))) := superpose eq9 eq29 -- superposition 29,9, 9 into 29, unify on (0).2 in 9 and (0).2.2.2.2 in 29
  have eq47 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq29 eq29 -- superposition 29,29, 29 into 29, unify on (0).2 in 29 and (0).2.2 in 29
  have eq48 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq9 eq29 -- superposition 29,9, 9 into 29, unify on (0).2 in 9 and (0).2 in 29
  have eq57 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq29 eq9 -- superposition 9,29, 29 into 9, unify on (0).2 in 29 and (0).2.2 in 9
  have eq62 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X0) ◇ X0) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq65 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq47 -- superposition 47,9, 9 into 47, unify on (0).2 in 9 and (0).2.2 in 47
  have eq66 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2.2 in 47
  have eq68 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq47 eq47 -- superposition 47,47, 47 into 47, unify on (0).2 in 47 and (0).2.2 in 47
  have eq70 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq29 eq47 -- superposition 47,29, 29 into 47, unify on (0).2 in 29 and (0).2 in 47
  have eq79 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq47 eq11 -- superposition 11,47, 47 into 11, unify on (0).2 in 47 and (0).2.2 in 11
  have eq80 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq47 eq9 -- superposition 9,47, 47 into 9, unify on (0).2 in 47 and (0).2.2 in 9
  have eq85 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq47 eq70 -- forward demodulation 70,47
  have eq86 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq85 eq62 -- backward demodulation 62,85
  have eq88 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq86 eq68 -- backward demodulation 68,86
  have eq89 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq88 eq65 -- backward demodulation 65,88
  have eq90 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq88 eq66 -- backward demodulation 66,88
  have eq97 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ X1) := superpose eq90 eq79 -- forward demodulation 79,90
  have eq99 (X0 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ X0)) := superpose eq97 eq37 -- backward demodulation 37,97
  have eq102 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq89 eq80 -- forward demodulation 80,89
  have eq104 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X1))) = ((X2 ◇ X2) ◇ X0) := superpose eq102 eq57 -- backward demodulation 57,102
  have eq105 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) := superpose eq102 eq12 -- backward demodulation 12,102
  have eq108 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq102 eq25 -- backward demodulation 25,102
  have eq110 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ ((X0 ◇ X0) ◇ X4)) := superpose eq102 eq32 -- backward demodulation 32,102
  have eq111 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq102 eq35 -- backward demodulation 35,102
  have eq128 (X0 X1 X2 X4 : G) : (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq105 eq105 -- superposition 105,105, 105 into 105, unify on (0).2 in 105 and (0).2.1.1 in 105
  have eq150 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq86 eq9 -- superposition 9,86, 86 into 9, unify on (0).2 in 86 and (0).2.2.1 in 9
  have eq178 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq99 eq99 -- superposition 99,99, 99 into 99, unify on (0).2 in 99 and (0).2.2 in 99
  have eq197 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq88 eq178 -- forward demodulation 178,88
  have eq198 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose eq99 eq197 -- forward demodulation 197,99
  have eq199 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq198 eq104 -- backward demodulation 104,198
  have eq200 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq198 eq108 -- backward demodulation 108,198
  have eq201 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X0 ◇ X4)) := superpose eq198 eq110 -- backward demodulation 110,198
  have eq204 (X0 X1 X2 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq198 eq128 -- backward demodulation 128,198
  have eq206 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq198 eq150 -- backward demodulation 150,198
  have eq210 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := superpose eq198 eq111 -- backward demodulation 111,198
  have eq211 (X0 X1 X2 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq199 eq200 -- forward demodulation 200,199
  have eq220 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq47 eq210 -- forward demodulation 210,47
  have eq245 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := superpose eq99 eq220 -- superposition 220,99, 99 into 220, unify on (0).2 in 99 and (0).2.1 in 220
  have eq250 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X2 ◇ X0)) := superpose eq9 eq220 -- superposition 220,9, 9 into 220, unify on (0).2 in 9 and (0).2.2 in 220
  have eq253 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) := superpose eq99 eq220 -- superposition 220,99, 99 into 220, unify on (0).2 in 99 and (0).2.2 in 220
  have eq283 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq198 eq245 -- forward demodulation 245,198
  have eq284 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq283 eq204 -- backward demodulation 204,283
  have eq289 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ X2) = (X4 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq284 eq211 -- backward demodulation 211,284
  have eq294 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X0 ◇ X4)) := superpose eq289 eq201 -- backward demodulation 201,289
  have eq299 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X2 ◇ X0)) := superpose eq289 eq250 -- forward demodulation 250,289
  have eq301 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X1)) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq198 eq253 -- forward demodulation 253,198
  have eq302 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq99 eq301 -- forward demodulation 301,99
  have eq303 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq302 eq206 -- backward demodulation 206,302
  have eq322 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ X0) := superpose eq303 eq299 -- backward demodulation 299,303
  have eq327 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ (X3 ◇ X2)) := superpose eq322 eq11 -- backward demodulation 11,322
  have eq340 (X0 X2 X3 X4 : G) : ((X2 ◇ X0) ◇ X3) = (((X2 ◇ X0) ◇ X3) ◇ (X0 ◇ X4)) := superpose eq322 eq294 -- backward demodulation 294,322
  have eq348 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ sK1)) := superpose eq322 eq10 -- backward demodulation 10,322
  have eq352 (X0 X2 X3 X4 : G) : (X3 ◇ X2) = ((X3 ◇ X2) ◇ (X0 ◇ X4)) := superpose eq322 eq340 -- forward demodulation 340,322
  have eq366 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq47 eq327 -- superposition 327,47, 47 into 327, unify on (0).2 in 47 and (0).2 in 327
  have eq380 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq366 eq348 -- backward demodulation 348,366
  have eq391 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq366 eq366 -- superposition 366,366, 366 into 366, unify on (0).2 in 366 and (0).1 in 366
  have eq602 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X4 ◇ (X2 ◇ X3)) := superpose eq352 eq391 -- superposition 391,352, 352 into 391, unify on (0).2 in 352 and (0).1 in 391
  have eq653 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq391 eq380 -- superposition 380,391, 391 into 380, unify on (0).2 in 391 and (0).2 in 380
  subsumption eq653 eq602


@[equational_result]
theorem Equation3561_implies_Equation3715 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3715 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq177 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq178 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq116 eq10 -- superposition 10,116, 116 into 10, unify on (0).2 in 116 and (0).2 in 10
  have eq179 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq177 -- forward demodulation 177,108
  subsumption eq178 eq179


@[equational_result]
theorem Equation3561_implies_Equation4165 (G : Type*) [Magma G] (h : Equation3561 G) : Equation4165 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq51 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq51 -- backward demodulation 51,94
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq126 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq108 eq10 -- backward demodulation 10,108
  subsumption eq126 eq108


@[equational_result]
theorem Equation3561_implies_Equation3577 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3577 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq126 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK3 ◇ sK0)) := superpose eq108 eq10 -- backward demodulation 10,108
  subsumption eq126 eq116


@[equational_result]
theorem Equation3561_implies_Equation4640 (G : Type*) [Magma G] (h : Equation3561 G) : Equation4640 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq30 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq31 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq9 eq31 -- forward demodulation 31,9
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq30 eq30 -- superposition 30,30, 30 into 30, unify on (0).2 in 30 and (0).2.2 in 30
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq30 eq9 -- superposition 9,30, 30 into 9, unify on (0).2 in 30 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq98 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq94 eq24 -- backward demodulation 24,94
  have eq106 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) := superpose eq95 eq35 -- backward demodulation 35,95
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq123 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq108 eq106 -- backward demodulation 106,108
  have eq126 : ((sK1 ◇ sK2) ◇ sK2) ≠ (sK1 ◇ sK0) := superpose eq108 eq10 -- backward demodulation 10,108
  have eq143 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X2 ◇ (X0 ◇ X4)) := superpose eq116 eq98 -- forward demodulation 98,116
  have eq144 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X4 ◇ X2) := superpose eq116 eq143 -- forward demodulation 143,116
  have eq145 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = (X4 ◇ X2) := superpose eq116 eq144 -- forward demodulation 144,116
  have eq146 (X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X1 ◇ X2) ◇ (X3 ◇ X4)) := superpose eq108 eq145 -- forward demodulation 145,108
  have eq175 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq176 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq175 -- forward demodulation 175,108
  have eq179 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq116 eq176 -- superposition 176,116, 116 into 176, unify on (0).2 in 116 and (0).1 in 176
  have eq192 (X0 : G) : (sK1 ◇ sK0) ≠ (X0 ◇ sK2) := superpose eq179 eq126 -- superposition 126,179, 179 into 126, unify on (0).2 in 179 and (0).1 in 126
  have eq203 (X0 X1 : G) : (X0 ◇ sK0) ≠ (X1 ◇ sK2) := superpose eq179 eq192 -- superposition 192,179, 179 into 192, unify on (0).2 in 179 and (0).1 in 192
  have eq246 (X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ X3) := superpose eq123 eq146 -- superposition 146,123, 123 into 146, unify on (0).2 in 123 and (0).2 in 146
  have eq268 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X1) := superpose eq179 eq246 -- superposition 246,179, 179 into 246, unify on (0).2 in 179 and (0).1 in 246
  have eq355 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq268 eq268 -- superposition 268,268, 268 into 268, unify on (0).2 in 268 and (0).1 in 268
  have eq391 (X0 X1 X2 : G) : (X1 ◇ X0) ≠ (X2 ◇ sK2) := superpose eq268 eq203 -- superposition 203,268, 268 into 203, unify on (0).2 in 268 and (0).1 in 203
  subsumption eq391 eq355


@[equational_result]
theorem Equation3561_implies_Equation41 (G : Type*) [Magma G] (h : Equation3561 G) : Equation41 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK1 ◇ sK2) ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq9 eq29 -- forward demodulation 29,9
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq98 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq94 eq24 -- backward demodulation 24,94
  have eq106 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) := superpose eq95 eq35 -- backward demodulation 35,95
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq123 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq108 eq106 -- backward demodulation 106,108
  have eq142 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X2 ◇ (X0 ◇ X4)) := superpose eq116 eq98 -- forward demodulation 98,116
  have eq143 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X4 ◇ X2) := superpose eq116 eq142 -- forward demodulation 142,116
  have eq144 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = (X4 ◇ X2) := superpose eq116 eq143 -- forward demodulation 143,116
  have eq145 (X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X1 ◇ X2) ◇ (X3 ◇ X4)) := superpose eq108 eq144 -- forward demodulation 144,108
  have eq177 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq178 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq177 -- forward demodulation 177,108
  have eq181 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq116 eq178 -- superposition 178,116, 116 into 178, unify on (0).2 in 116 and (0).1 in 178
  have eq193 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK2) := superpose eq181 eq10 -- superposition 10,181, 181 into 10, unify on (0).2 in 181 and (0).1 in 10
  have eq226 (X0 X1 : G) : (X0 ◇ sK0) ≠ (X1 ◇ sK2) := superpose eq181 eq193 -- superposition 193,181, 181 into 193, unify on (0).2 in 181 and (0).1 in 193
  have eq242 (X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ X3) := superpose eq123 eq145 -- superposition 145,123, 123 into 145, unify on (0).2 in 123 and (0).2 in 145
  have eq262 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X1) := superpose eq181 eq242 -- superposition 242,181, 181 into 242, unify on (0).2 in 181 and (0).1 in 242
  have eq422 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq262 eq262 -- superposition 262,262, 262 into 262, unify on (0).2 in 262 and (0).1 in 262
  have eq461 (X0 X1 X2 : G) : (X1 ◇ X0) ≠ (X2 ◇ sK2) := superpose eq262 eq226 -- superposition 226,262, 262 into 226, unify on (0).2 in 262 and (0).1 in 226
  subsumption eq461 eq422


@[equational_result]
theorem Equation3561_implies_Equation3617 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3617 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK2 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.1 in 11
  have eq25 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq28 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq29 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq32 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2.1 in 9
  have eq35 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq9 eq28 -- forward demodulation 28,9
  have eq37 (X0 X2 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X0)))) := superpose eq9 eq29 -- superposition 29,9, 9 into 29, unify on (0).2 in 9 and (0).2.2.2.2 in 29
  have eq47 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq29 eq29 -- superposition 29,29, 29 into 29, unify on (0).2 in 29 and (0).2.2 in 29
  have eq48 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq9 eq29 -- superposition 29,9, 9 into 29, unify on (0).2 in 9 and (0).2 in 29
  have eq57 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq29 eq9 -- superposition 9,29, 29 into 9, unify on (0).2 in 29 and (0).2.2 in 9
  have eq62 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X0) ◇ X0) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq65 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq47 -- superposition 47,9, 9 into 47, unify on (0).2 in 9 and (0).2.2 in 47
  have eq66 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2.2 in 47
  have eq68 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq47 eq47 -- superposition 47,47, 47 into 47, unify on (0).2 in 47 and (0).2.2 in 47
  have eq70 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq29 eq47 -- superposition 47,29, 29 into 47, unify on (0).2 in 29 and (0).2 in 47
  have eq79 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq47 eq11 -- superposition 11,47, 47 into 11, unify on (0).2 in 47 and (0).2.2 in 11
  have eq80 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq47 eq9 -- superposition 9,47, 47 into 9, unify on (0).2 in 47 and (0).2.2 in 9
  have eq85 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq47 eq70 -- forward demodulation 70,47
  have eq86 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq85 eq62 -- backward demodulation 62,85
  have eq88 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq86 eq68 -- backward demodulation 68,86
  have eq89 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq88 eq65 -- backward demodulation 65,88
  have eq90 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq88 eq66 -- backward demodulation 66,88
  have eq97 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ X1) := superpose eq90 eq79 -- forward demodulation 79,90
  have eq99 (X0 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ X0)) := superpose eq97 eq37 -- backward demodulation 37,97
  have eq102 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq89 eq80 -- forward demodulation 80,89
  have eq104 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X1))) = ((X2 ◇ X2) ◇ X0) := superpose eq102 eq57 -- backward demodulation 57,102
  have eq105 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ X0) := superpose eq102 eq12 -- backward demodulation 12,102
  have eq108 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq102 eq25 -- backward demodulation 25,102
  have eq110 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ ((X0 ◇ X0) ◇ X4)) := superpose eq102 eq32 -- backward demodulation 32,102
  have eq111 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq102 eq35 -- backward demodulation 35,102
  have eq128 (X0 X1 X2 X4 : G) : (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq105 eq105 -- superposition 105,105, 105 into 105, unify on (0).2 in 105 and (0).1.1.1 in 105
  have eq150 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq86 eq9 -- superposition 9,86, 86 into 9, unify on (0).2 in 86 and (0).2.2.1 in 9
  have eq178 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq99 eq99 -- superposition 99,99, 99 into 99, unify on (0).2 in 99 and (0).2.2 in 99
  have eq197 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq88 eq178 -- forward demodulation 178,88
  have eq198 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose eq99 eq197 -- forward demodulation 197,99
  have eq199 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq198 eq104 -- backward demodulation 104,198
  have eq200 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq198 eq108 -- backward demodulation 108,198
  have eq201 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X0 ◇ X4)) := superpose eq198 eq110 -- backward demodulation 110,198
  have eq204 (X0 X1 X2 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq198 eq128 -- backward demodulation 128,198
  have eq206 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq198 eq150 -- backward demodulation 150,198
  have eq210 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := superpose eq198 eq111 -- backward demodulation 111,198
  have eq211 (X0 X1 X2 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq199 eq200 -- forward demodulation 200,199
  have eq220 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq47 eq210 -- forward demodulation 210,47
  have eq245 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := superpose eq99 eq220 -- superposition 220,99, 99 into 220, unify on (0).2 in 99 and (0).2.1 in 220
  have eq250 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X2 ◇ X0)) := superpose eq9 eq220 -- superposition 220,9, 9 into 220, unify on (0).2 in 9 and (0).2.2 in 220
  have eq253 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) := superpose eq99 eq220 -- superposition 220,99, 99 into 220, unify on (0).2 in 99 and (0).2.2 in 220
  have eq283 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq198 eq245 -- forward demodulation 245,198
  have eq284 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq283 eq204 -- backward demodulation 204,283
  have eq289 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ X2) = (X4 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq284 eq211 -- backward demodulation 211,284
  have eq292 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq289 eq14 -- backward demodulation 14,289
  have eq294 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X0 ◇ X4)) := superpose eq289 eq201 -- backward demodulation 201,289
  have eq299 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X2 ◇ X0)) := superpose eq289 eq250 -- forward demodulation 250,289
  have eq301 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X1)) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq198 eq253 -- forward demodulation 253,198
  have eq302 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq99 eq301 -- forward demodulation 301,99
  have eq303 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq302 eq206 -- backward demodulation 206,302
  have eq322 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ X2) := superpose eq303 eq299 -- backward demodulation 299,303
  have eq327 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ (X3 ◇ X2)) := superpose eq322 eq11 -- backward demodulation 11,322
  have eq339 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq322 eq292 -- backward demodulation 292,322
  have eq340 (X0 X2 X3 X4 : G) : ((X2 ◇ X0) ◇ X3) = (((X2 ◇ X0) ◇ X3) ◇ (X0 ◇ X4)) := superpose eq322 eq294 -- backward demodulation 294,322
  have eq348 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ sK2)) := superpose eq322 eq10 -- backward demodulation 10,322
  have eq350 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X0) ◇ (X3 ◇ X2)) := superpose eq322 eq339 -- forward demodulation 339,322
  have eq351 (X0 X2 X3 X4 : G) : (X3 ◇ X2) = ((X3 ◇ X2) ◇ (X0 ◇ X4)) := superpose eq322 eq340 -- forward demodulation 340,322
  have eq365 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq47 eq327 -- superposition 327,47, 47 into 327, unify on (0).2 in 47 and (0).2 in 327
  have eq392 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq365 eq365 -- superposition 365,365, 365 into 365, unify on (0).2 in 365 and (0).2 in 365
  have eq428 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq220 eq350 -- superposition 350,220, 220 into 350, unify on (0).2 in 220 and (0).2 in 350
  have eq452 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ X1) := superpose eq365 eq428 -- superposition 428,365, 365 into 428, unify on (0).2 in 365 and (0).1 in 428
  have eq485 : (sK2 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK0) := superpose eq452 eq348 -- backward demodulation 348,452
  have eq487 : (sK0 ◇ sK0) ≠ (sK2 ◇ (sK1 ◇ sK1)) := superpose eq452 eq485 -- forward demodulation 485,452
  have eq545 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X4 ◇ (X2 ◇ X3)) := superpose eq351 eq392 -- superposition 392,351, 351 into 392, unify on (0).2 in 351 and (0).1 in 392
  have eq589 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq392 eq487 -- superposition 487,392, 392 into 487, unify on (0).2 in 392 and (0).2 in 487
  subsumption eq589 eq545


@[equational_result]
theorem Equation3561_implies_Equation3479 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3479 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK0 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq30 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq31 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq9 eq31 -- forward demodulation 31,9
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq30 eq30 -- superposition 30,30, 30 into 30, unify on (0).2 in 30 and (0).2.2 in 30
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq30 eq9 -- superposition 9,30, 30 into 9, unify on (0).2 in 30 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq98 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq94 eq24 -- backward demodulation 24,94
  have eq106 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) := superpose eq95 eq35 -- backward demodulation 35,95
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq123 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq108 eq106 -- backward demodulation 106,108
  have eq126 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ sK2)) := superpose eq108 eq10 -- backward demodulation 10,108
  have eq143 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X2 ◇ (X0 ◇ X4)) := superpose eq116 eq98 -- forward demodulation 98,116
  have eq144 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X4 ◇ X2) := superpose eq116 eq143 -- forward demodulation 143,116
  have eq145 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = (X4 ◇ X2) := superpose eq116 eq144 -- forward demodulation 144,116
  have eq146 (X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X1 ◇ X2) ◇ (X3 ◇ X4)) := superpose eq108 eq145 -- forward demodulation 145,108
  have eq175 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq176 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK1) := superpose eq116 eq126 -- superposition 126,116, 116 into 126, unify on (0).2 in 116 and (0).2 in 126
  have eq177 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq175 -- forward demodulation 175,108
  have eq180 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq116 eq177 -- superposition 177,116, 116 into 177, unify on (0).2 in 116 and (0).1 in 177
  have eq194 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK1) := superpose eq180 eq176 -- superposition 176,180, 180 into 176, unify on (0).2 in 180 and (0).2 in 176
  have eq230 (X0 X1 : G) : (X0 ◇ sK0) ≠ (X1 ◇ sK1) := superpose eq180 eq194 -- superposition 194,180, 180 into 194, unify on (0).2 in 180 and (0).1 in 194
  have eq246 (X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ X3) := superpose eq123 eq146 -- superposition 146,123, 123 into 146, unify on (0).2 in 123 and (0).2 in 146
  have eq266 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X1) := superpose eq180 eq246 -- superposition 246,180, 180 into 246, unify on (0).2 in 180 and (0).1 in 246
  have eq467 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq266 eq266 -- superposition 266,266, 266 into 266, unify on (0).2 in 266 and (0).1 in 266
  have eq507 (X0 X1 X2 : G) : (X1 ◇ X0) ≠ (X2 ◇ sK1) := superpose eq266 eq230 -- superposition 230,266, 266 into 230, unify on (0).2 in 266 and (0).1 in 230
  subsumption eq507 eq467


@[equational_result]
theorem Equation3561_implies_Equation4154 (G : Type*) [Magma G] (h : Equation3561 G) : Equation4154 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq30 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq31 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq9 eq31 -- forward demodulation 31,9
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq30 eq30 -- superposition 30,30, 30 into 30, unify on (0).2 in 30 and (0).2.2 in 30
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq30 eq9 -- superposition 9,30, 30 into 9, unify on (0).2 in 30 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq98 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq94 eq24 -- backward demodulation 24,94
  have eq106 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) := superpose eq95 eq35 -- backward demodulation 35,95
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq123 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq108 eq106 -- backward demodulation 106,108
  have eq126 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq108 eq10 -- backward demodulation 10,108
  have eq143 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X2 ◇ (X0 ◇ X4)) := superpose eq116 eq98 -- forward demodulation 98,116
  have eq144 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X4 ◇ X2) := superpose eq116 eq143 -- forward demodulation 143,116
  have eq145 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = (X4 ◇ X2) := superpose eq116 eq144 -- forward demodulation 144,116
  have eq146 (X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X1 ◇ X2) ◇ (X3 ◇ X4)) := superpose eq108 eq145 -- forward demodulation 145,108
  have eq175 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq176 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq175 -- forward demodulation 175,108
  have eq179 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq116 eq176 -- superposition 176,116, 116 into 176, unify on (0).2 in 116 and (0).1 in 176
  have eq244 (X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ X3) := superpose eq123 eq146 -- superposition 146,123, 123 into 146, unify on (0).2 in 123 and (0).2 in 146
  have eq264 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X1) := superpose eq179 eq244 -- superposition 244,179, 179 into 244, unify on (0).2 in 179 and (0).1 in 244
  have eq354 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq264 eq126 -- superposition 126,264, 264 into 126, unify on (0).2 in 264 and (0).1 in 126
  subsumption eq354 eq264


@[equational_result]
theorem Equation3561_implies_Equation3417 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3417 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq132 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK2)) := superpose eq116 eq10 -- backward demodulation 10,116
  have eq178 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq180 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq178 -- forward demodulation 178,108
  have eq183 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq116 eq180 -- superposition 180,116, 116 into 180, unify on (0).2 in 116 and (0).1 in 180
  have eq188 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (X3 ◇ (X1 ◇ X2)) := superpose eq180 eq183 -- superposition 183,180, 180 into 183, unify on (0).2 in 180 and (0).1 in 183
  have eq198 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK0 ◇ sK2)) := superpose eq183 eq132 -- superposition 132,183, 183 into 132, unify on (0).2 in 183 and (0).2 in 132
  subsumption eq198 eq188


@[equational_result]
theorem Equation3561_implies_Equation373 (G : Type*) [Magma G] (h : Equation3561 G) : Equation373 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ sK3) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq9 eq29 -- forward demodulation 29,9
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq51 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq51 -- backward demodulation 51,94
  have eq98 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq94 eq24 -- backward demodulation 24,94
  have eq106 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) := superpose eq95 eq35 -- backward demodulation 35,95
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq123 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq108 eq106 -- backward demodulation 106,108
  have eq142 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X2 ◇ (X0 ◇ X4)) := superpose eq116 eq98 -- forward demodulation 98,116
  have eq143 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X4 ◇ X2) := superpose eq116 eq142 -- forward demodulation 142,116
  have eq144 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = (X4 ◇ X2) := superpose eq116 eq143 -- forward demodulation 143,116
  have eq145 (X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X1 ◇ X2) ◇ (X3 ◇ X4)) := superpose eq108 eq144 -- forward demodulation 144,108
  have eq177 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq178 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq177 -- forward demodulation 177,108
  have eq181 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq116 eq178 -- superposition 178,116, 116 into 178, unify on (0).2 in 116 and (0).1 in 178
  have eq194 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK3) := superpose eq181 eq10 -- superposition 10,181, 181 into 10, unify on (0).2 in 181 and (0).2 in 10
  have eq228 (X0 X1 : G) : (X0 ◇ sK0) ≠ (X1 ◇ sK3) := superpose eq181 eq194 -- superposition 194,181, 181 into 194, unify on (0).2 in 181 and (0).1 in 194
  have eq244 (X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ X3) := superpose eq123 eq145 -- superposition 145,123, 123 into 145, unify on (0).2 in 123 and (0).2 in 145
  have eq264 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X1) := superpose eq181 eq244 -- superposition 244,181, 181 into 244, unify on (0).2 in 181 and (0).1 in 244
  have eq397 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq264 eq264 -- superposition 264,264, 264 into 264, unify on (0).2 in 264 and (0).1 in 264
  have eq433 (X0 X1 X2 : G) : (X1 ◇ X0) ≠ (X2 ◇ sK3) := superpose eq264 eq228 -- superposition 228,264, 264 into 228, unify on (0).2 in 264 and (0).1 in 228
  subsumption eq433 eq397


@[equational_result]
theorem Equation3561_implies_Equation3492 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3492 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq126 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq108 eq10 -- backward demodulation 10,108
  have eq178 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq180 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq178 -- forward demodulation 178,108
  have eq183 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq116 eq180 -- superposition 180,116, 116 into 180, unify on (0).2 in 116 and (0).1 in 180
  have eq188 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (X3 ◇ (X1 ◇ X2)) := superpose eq180 eq183 -- superposition 183,180, 180 into 183, unify on (0).2 in 180 and (0).1 in 183
  have eq198 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq183 eq126 -- superposition 126,183, 183 into 126, unify on (0).2 in 183 and (0).2 in 126
  subsumption eq198 eq188


@[equational_result]
theorem Equation3561_implies_Equation3331 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3331 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq9 eq29 -- forward demodulation 29,9
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq98 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq94 eq24 -- backward demodulation 24,94
  have eq106 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) := superpose eq95 eq35 -- backward demodulation 35,95
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq123 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq108 eq106 -- backward demodulation 106,108
  have eq132 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq116 eq10 -- backward demodulation 10,116
  have eq143 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X2 ◇ (X0 ◇ X4)) := superpose eq116 eq98 -- forward demodulation 98,116
  have eq144 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X4 ◇ X2) := superpose eq116 eq143 -- forward demodulation 143,116
  have eq145 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = (X4 ◇ X2) := superpose eq116 eq144 -- forward demodulation 144,116
  have eq146 (X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X1 ◇ X2) ◇ (X3 ◇ X4)) := superpose eq108 eq145 -- forward demodulation 145,108
  have eq178 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq179 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK0) := superpose eq116 eq132 -- superposition 132,116, 116 into 132, unify on (0).2 in 116 and (0).2 in 132
  have eq180 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq178 -- forward demodulation 178,108
  have eq183 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq116 eq180 -- superposition 180,116, 116 into 180, unify on (0).2 in 116 and (0).1 in 180
  have eq197 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK0) := superpose eq183 eq179 -- superposition 179,183, 183 into 179, unify on (0).2 in 183 and (0).2 in 179
  have eq249 (X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ X3) := superpose eq123 eq146 -- superposition 146,123, 123 into 146, unify on (0).2 in 123 and (0).2 in 146
  have eq289 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ X0) := superpose eq249 eq197 -- superposition 197,249, 249 into 197, unify on (0).2 in 249 and (0).2 in 197
  subsumption eq289 rfl


@[equational_result]
theorem Equation3561_implies_Equation3748 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3748 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq30 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq31 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq9 eq31 -- forward demodulation 31,9
  have eq45 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq11 eq30 -- superposition 30,11, 11 into 30, unify on (0).2 in 11 and (0).2.2 in 30
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq30 eq30 -- superposition 30,30, 30 into 30, unify on (0).2 in 30 and (0).2.2 in 30
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq30 eq9 -- superposition 9,30, 30 into 9, unify on (0).2 in 30 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq98 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq94 eq24 -- backward demodulation 24,94
  have eq106 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) := superpose eq95 eq35 -- backward demodulation 35,95
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq111 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq108 eq45 -- backward demodulation 45,108
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq123 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq108 eq106 -- backward demodulation 106,108
  have eq131 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq116 eq111 -- backward demodulation 111,116
  have eq132 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq131 eq10 -- backward demodulation 10,131
  have eq143 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X2 ◇ (X0 ◇ X4)) := superpose eq116 eq98 -- forward demodulation 98,116
  have eq144 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X4 ◇ X2) := superpose eq116 eq143 -- forward demodulation 143,116
  have eq145 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = (X4 ◇ X2) := superpose eq116 eq144 -- forward demodulation 144,116
  have eq146 (X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X1 ◇ X2) ◇ (X3 ◇ X4)) := superpose eq108 eq145 -- forward demodulation 145,108
  have eq175 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq176 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq175 -- forward demodulation 175,108
  have eq179 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq116 eq176 -- superposition 176,116, 116 into 176, unify on (0).2 in 116 and (0).1 in 176
  have eq244 (X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ X3) := superpose eq123 eq146 -- superposition 146,123, 123 into 146, unify on (0).2 in 123 and (0).2 in 146
  have eq264 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X1) := superpose eq179 eq244 -- superposition 244,179, 179 into 244, unify on (0).2 in 179 and (0).1 in 244
  have eq354 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq264 eq132 -- superposition 132,264, 264 into 132, unify on (0).2 in 264 and (0).1 in 132
  subsumption eq354 eq264


@[equational_result]
theorem Equation3561_implies_Equation309 (G : Type*) [Magma G] (h : Equation3561 G) : Equation309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq178 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq116 eq10 -- superposition 10,116, 116 into 10, unify on (0).2 in 116 and (0).2 in 10
  subsumption eq178 rfl


@[equational_result]
theorem Equation3561_implies_Equation3551 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3551 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK0 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq126 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq108 eq10 -- backward demodulation 10,108
  subsumption eq126 eq116


@[equational_result]
theorem Equation3561_implies_Equation3566 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3566 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq126 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq108 eq10 -- backward demodulation 10,108
  have eq178 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq180 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq178 -- forward demodulation 178,108
  have eq184 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq180 eq126 -- superposition 126,180, 180 into 126, unify on (0).2 in 180 and (0).2 in 126
  subsumption eq184 rfl


@[equational_result]
theorem Equation3561_implies_Equation3940 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3940 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq9 eq29 -- forward demodulation 29,9
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq98 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq94 eq24 -- backward demodulation 24,94
  have eq106 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) := superpose eq95 eq35 -- backward demodulation 35,95
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq123 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq108 eq106 -- backward demodulation 106,108
  have eq132 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK2) := superpose eq116 eq10 -- backward demodulation 10,116
  have eq143 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X2 ◇ (X0 ◇ X4)) := superpose eq116 eq98 -- forward demodulation 98,116
  have eq144 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X4 ◇ X2) := superpose eq116 eq143 -- forward demodulation 143,116
  have eq145 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = (X4 ◇ X2) := superpose eq116 eq144 -- forward demodulation 144,116
  have eq146 (X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X1 ◇ X2) ◇ (X3 ◇ X4)) := superpose eq108 eq145 -- forward demodulation 145,108
  have eq178 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq179 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq178 -- forward demodulation 178,108
  have eq182 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq116 eq179 -- superposition 179,116, 116 into 179, unify on (0).2 in 116 and (0).1 in 179
  have eq195 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK2) := superpose eq182 eq132 -- superposition 132,182, 182 into 132, unify on (0).2 in 182 and (0).2 in 132
  have eq206 (X0 X1 : G) : (X0 ◇ sK1) ≠ (X1 ◇ sK2) := superpose eq182 eq195 -- superposition 195,182, 182 into 195, unify on (0).2 in 182 and (0).1 in 195
  have eq249 (X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ X3) := superpose eq123 eq146 -- superposition 146,123, 123 into 146, unify on (0).2 in 123 and (0).2 in 146
  have eq270 (X0 X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ X0) := superpose eq182 eq249 -- superposition 249,182, 182 into 249, unify on (0).2 in 182 and (0).1 in 249
  have eq321 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq270 eq270 -- superposition 270,270, 270 into 270, unify on (0).2 in 270 and (0).1 in 270
  have eq371 (X0 X1 X2 : G) : (X1 ◇ X0) ≠ (X2 ◇ sK2) := superpose eq270 eq206 -- superposition 206,270, 270 into 206, unify on (0).2 in 270 and (0).1 in 206
  subsumption eq371 eq321


@[equational_result]
theorem Equation3561_implies_Equation3345 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3345 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq132 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq116 eq10 -- backward demodulation 10,116
  subsumption eq132 eq116


@[equational_result]
theorem Equation3561_implies_Equation3919 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3919 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.1 in 11
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq27 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq34 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq9 eq27 -- forward demodulation 27,9
  have eq36 (X0 X2 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X0)))) := superpose eq9 eq28 -- superposition 28,9, 9 into 28, unify on (0).2 in 9 and (0).2.2.2.2 in 28
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq47 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq9 eq28 -- superposition 28,9, 9 into 28, unify on (0).2 in 9 and (0).2 in 28
  have eq51 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq61 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK2) := superpose eq46 eq10 -- backward demodulation 10,46
  have eq62 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X0) ◇ X0) := superpose eq9 eq47 -- forward demodulation 47,9
  have eq65 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq46 -- superposition 46,9, 9 into 46, unify on (0).2 in 9 and (0).2.2 in 46
  have eq66 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq11 eq46 -- superposition 46,11, 11 into 46, unify on (0).2 in 11 and (0).2.2 in 46
  have eq68 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq46 eq46 -- superposition 46,46, 46 into 46, unify on (0).2 in 46 and (0).2.2 in 46
  have eq70 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq28 eq46 -- superposition 46,28, 28 into 46, unify on (0).2 in 28 and (0).2 in 46
  have eq79 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq46 eq11 -- superposition 11,46, 46 into 11, unify on (0).2 in 46 and (0).2.2 in 11
  have eq80 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq46 eq9 -- superposition 9,46, 46 into 9, unify on (0).2 in 46 and (0).2.2 in 9
  have eq85 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq46 eq70 -- forward demodulation 70,46
  have eq86 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq85 eq62 -- backward demodulation 62,85
  have eq88 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq86 eq68 -- backward demodulation 68,86
  have eq89 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq88 eq65 -- backward demodulation 65,88
  have eq90 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq88 eq66 -- backward demodulation 66,88
  have eq97 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ X1) := superpose eq90 eq79 -- forward demodulation 79,90
  have eq99 (X0 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ X0)) := superpose eq97 eq36 -- backward demodulation 36,97
  have eq102 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq89 eq80 -- forward demodulation 80,89
  have eq104 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X1))) = ((X2 ◇ X2) ◇ X0) := superpose eq102 eq51 -- backward demodulation 51,102
  have eq105 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ X0) := superpose eq102 eq12 -- backward demodulation 12,102
  have eq108 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq102 eq24 -- backward demodulation 24,102
  have eq111 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq102 eq34 -- backward demodulation 34,102
  have eq128 (X0 X1 X2 X4 : G) : (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq105 eq105 -- superposition 105,105, 105 into 105, unify on (0).2 in 105 and (0).1.1.1 in 105
  have eq150 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq86 eq9 -- superposition 9,86, 86 into 9, unify on (0).2 in 86 and (0).2.2.1 in 9
  have eq178 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq99 eq99 -- superposition 99,99, 99 into 99, unify on (0).2 in 99 and (0).2.2 in 99
  have eq197 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq88 eq178 -- forward demodulation 178,88
  have eq198 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose eq99 eq197 -- forward demodulation 197,99
  have eq199 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq198 eq104 -- backward demodulation 104,198
  have eq200 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq198 eq108 -- backward demodulation 108,198
  have eq204 (X0 X1 X2 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq198 eq128 -- backward demodulation 128,198
  have eq206 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq198 eq150 -- backward demodulation 150,198
  have eq210 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq198 eq111 -- backward demodulation 111,198
  have eq211 (X0 X1 X2 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq199 eq200 -- forward demodulation 200,199
  have eq220 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq46 eq210 -- forward demodulation 210,46
  have eq245 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := superpose eq99 eq220 -- superposition 220,99, 99 into 220, unify on (0).2 in 99 and (0).2.1 in 220
  have eq250 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X2 ◇ X0)) := superpose eq9 eq220 -- superposition 220,9, 9 into 220, unify on (0).2 in 9 and (0).2.2 in 220
  have eq253 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) := superpose eq99 eq220 -- superposition 220,99, 99 into 220, unify on (0).2 in 99 and (0).2.2 in 220
  have eq283 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq198 eq245 -- forward demodulation 245,198
  have eq284 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq283 eq204 -- backward demodulation 204,283
  have eq289 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ X2) = (X4 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq284 eq211 -- backward demodulation 211,284
  have eq292 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq289 eq13 -- backward demodulation 13,289
  have eq299 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X2 ◇ X0)) := superpose eq289 eq250 -- forward demodulation 250,289
  have eq301 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X1)) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq198 eq253 -- forward demodulation 253,198
  have eq302 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq99 eq301 -- forward demodulation 301,99
  have eq303 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq302 eq206 -- backward demodulation 206,302
  have eq322 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ X0) := superpose eq303 eq299 -- backward demodulation 299,303
  have eq327 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ (X3 ◇ X2)) := superpose eq322 eq11 -- backward demodulation 11,322
  have eq339 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq322 eq292 -- backward demodulation 292,322
  have eq349 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X0) ◇ (X3 ◇ X2)) := superpose eq322 eq339 -- forward demodulation 339,322
  have eq364 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq46 eq327 -- superposition 327,46, 46 into 327, unify on (0).2 in 46 and (0).2 in 327
  have eq377 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq364 eq61 -- backward demodulation 61,364
  have eq429 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq220 eq349 -- superposition 349,220, 220 into 349, unify on (0).2 in 220 and (0).2 in 349
  have eq453 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ X1) := superpose eq364 eq429 -- superposition 429,364, 364 into 429, unify on (0).2 in 364 and (0).1 in 429
  have eq473 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK0)) := superpose eq429 eq377 -- superposition 377,429, 429 into 377, unify on (0).2 in 429 and (0).2 in 377
  have eq491 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq303 eq473 -- forward demodulation 473,303
  subsumption eq491 eq453


@[equational_result]
theorem Equation3561_implies_Equation384 (G : Type*) [Magma G] (h : Equation3561 G) : Equation384 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq30 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq31 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq9 eq31 -- forward demodulation 31,9
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq30 eq30 -- superposition 30,30, 30 into 30, unify on (0).2 in 30 and (0).2.2 in 30
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq30 eq9 -- superposition 9,30, 30 into 9, unify on (0).2 in 30 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq98 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq94 eq24 -- backward demodulation 24,94
  have eq106 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) := superpose eq95 eq35 -- backward demodulation 35,95
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq123 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq108 eq106 -- backward demodulation 106,108
  have eq126 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq108 eq10 -- backward demodulation 10,108
  have eq143 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X2 ◇ (X0 ◇ X4)) := superpose eq116 eq98 -- forward demodulation 98,116
  have eq144 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X4 ◇ X2) := superpose eq116 eq143 -- forward demodulation 143,116
  have eq145 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = (X4 ◇ X2) := superpose eq116 eq144 -- forward demodulation 144,116
  have eq146 (X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X1 ◇ X2) ◇ (X3 ◇ X4)) := superpose eq108 eq145 -- forward demodulation 145,108
  have eq175 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq176 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq175 -- forward demodulation 175,108
  have eq179 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq116 eq176 -- superposition 176,116, 116 into 176, unify on (0).2 in 116 and (0).1 in 176
  have eq244 (X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ X3) := superpose eq123 eq146 -- superposition 146,123, 123 into 146, unify on (0).2 in 123 and (0).2 in 146
  have eq264 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X1) := superpose eq179 eq244 -- superposition 244,179, 179 into 244, unify on (0).2 in 179 and (0).1 in 244
  have eq354 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq264 eq126 -- superposition 126,264, 264 into 126, unify on (0).2 in 264 and (0).1 in 126
  subsumption eq354 eq264


@[equational_result]
theorem Equation3561_implies_Equation365 (G : Type*) [Magma G] (h : Equation3561 G) : Equation365 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq9 eq29 -- forward demodulation 29,9
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq51 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq51 -- backward demodulation 51,94
  have eq98 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq94 eq24 -- backward demodulation 24,94
  have eq106 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) := superpose eq95 eq35 -- backward demodulation 35,95
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq123 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq108 eq106 -- backward demodulation 106,108
  have eq142 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X2 ◇ (X0 ◇ X4)) := superpose eq116 eq98 -- forward demodulation 98,116
  have eq143 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X4 ◇ X2) := superpose eq116 eq142 -- forward demodulation 142,116
  have eq144 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = (X4 ◇ X2) := superpose eq116 eq143 -- forward demodulation 143,116
  have eq145 (X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X1 ◇ X2) ◇ (X3 ◇ X4)) := superpose eq108 eq144 -- forward demodulation 144,108
  have eq176 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq177 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq176 -- forward demodulation 176,108
  have eq180 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq116 eq177 -- superposition 177,116, 116 into 177, unify on (0).2 in 116 and (0).1 in 177
  have eq193 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK1) := superpose eq180 eq10 -- superposition 10,180, 180 into 10, unify on (0).2 in 180 and (0).2 in 10
  have eq230 (X0 X1 : G) : (X0 ◇ sK0) ≠ (X1 ◇ sK1) := superpose eq180 eq193 -- superposition 193,180, 180 into 193, unify on (0).2 in 180 and (0).1 in 193
  have eq246 (X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ X3) := superpose eq123 eq145 -- superposition 145,123, 123 into 145, unify on (0).2 in 123 and (0).2 in 145
  have eq267 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X1) := superpose eq180 eq246 -- superposition 246,180, 180 into 246, unify on (0).2 in 180 and (0).1 in 246
  have eq397 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq267 eq267 -- superposition 267,267, 267 into 267, unify on (0).2 in 267 and (0).1 in 267
  have eq433 (X0 X1 X2 : G) : (X1 ◇ X0) ≠ (X2 ◇ sK1) := superpose eq267 eq230 -- superposition 230,267, 267 into 230, unify on (0).2 in 267 and (0).1 in 230
  subsumption eq433 eq397


@[equational_result]
theorem Equation3561_implies_Equation3482 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3482 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq25 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq28 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq29 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq32 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2.1 in 9
  have eq35 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq9 eq28 -- forward demodulation 28,9
  have eq37 (X0 X2 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X0)))) := superpose eq9 eq29 -- superposition 29,9, 9 into 29, unify on (0).2 in 9 and (0).2.2.2.2 in 29
  have eq47 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq29 eq29 -- superposition 29,29, 29 into 29, unify on (0).2 in 29 and (0).2.2 in 29
  have eq48 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq9 eq29 -- superposition 29,9, 9 into 29, unify on (0).2 in 9 and (0).2 in 29
  have eq52 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq29 eq9 -- superposition 9,29, 29 into 9, unify on (0).2 in 29 and (0).2.2 in 9
  have eq62 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X0) ◇ X0) := superpose eq9 eq48 -- forward demodulation 48,9
  have eq65 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq47 -- superposition 47,9, 9 into 47, unify on (0).2 in 9 and (0).2.2 in 47
  have eq66 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2.2 in 47
  have eq68 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq47 eq47 -- superposition 47,47, 47 into 47, unify on (0).2 in 47 and (0).2.2 in 47
  have eq70 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq29 eq47 -- superposition 47,29, 29 into 47, unify on (0).2 in 29 and (0).2 in 47
  have eq72 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq47 eq11 -- superposition 11,47, 47 into 11, unify on (0).2 in 47 and (0).2.2 in 11
  have eq73 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq47 eq9 -- superposition 9,47, 47 into 9, unify on (0).2 in 47 and (0).2.2 in 9
  have eq85 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := superpose eq68 eq10 -- backward demodulation 10,68
  have eq86 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq47 eq70 -- forward demodulation 70,47
  have eq87 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq86 eq62 -- backward demodulation 62,86
  have eq89 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq87 eq68 -- backward demodulation 68,87
  have eq90 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq89 eq65 -- backward demodulation 65,89
  have eq91 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq89 eq66 -- backward demodulation 66,89
  have eq96 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq89 eq85 -- backward demodulation 85,89
  have eq98 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ X1) := superpose eq91 eq72 -- forward demodulation 72,91
  have eq100 (X0 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ X0)) := superpose eq98 eq37 -- backward demodulation 37,98
  have eq103 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq90 eq73 -- forward demodulation 73,90
  have eq105 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X1))) = ((X2 ◇ X2) ◇ X0) := superpose eq103 eq52 -- backward demodulation 52,103
  have eq106 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) := superpose eq103 eq12 -- backward demodulation 12,103
  have eq109 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq103 eq25 -- backward demodulation 25,103
  have eq111 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ ((X0 ◇ X0) ◇ X4)) := superpose eq103 eq32 -- backward demodulation 32,103
  have eq112 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq103 eq35 -- backward demodulation 35,103
  have eq133 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq87 eq9 -- superposition 9,87, 87 into 9, unify on (0).2 in 87 and (0).2.2.1 in 9
  have eq143 (X0 X1 X2 X4 : G) : (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq106 eq106 -- superposition 106,106, 106 into 106, unify on (0).2 in 106 and (0).2.1.1 in 106
  have eq155 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq100 eq100 -- superposition 100,100, 100 into 100, unify on (0).2 in 100 and (0).2.2 in 100
  have eq170 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq89 eq155 -- forward demodulation 155,89
  have eq171 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose eq100 eq170 -- forward demodulation 170,100
  have eq172 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq171 eq105 -- backward demodulation 105,171
  have eq173 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq171 eq109 -- backward demodulation 109,171
  have eq174 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X0 ◇ X4)) := superpose eq171 eq111 -- backward demodulation 111,171
  have eq176 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq171 eq133 -- backward demodulation 133,171
  have eq179 (X0 X1 X2 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq171 eq143 -- backward demodulation 143,171
  have eq180 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := superpose eq171 eq112 -- backward demodulation 112,171
  have eq181 (X0 X1 X2 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq172 eq173 -- forward demodulation 173,172
  have eq184 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq47 eq180 -- forward demodulation 180,47
  have eq203 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := superpose eq100 eq184 -- superposition 184,100, 100 into 184, unify on (0).2 in 100 and (0).2.1 in 184
  have eq207 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X2 ◇ X0)) := superpose eq9 eq184 -- superposition 184,9, 9 into 184, unify on (0).2 in 9 and (0).2.2 in 184
  have eq210 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) := superpose eq100 eq184 -- superposition 184,100, 100 into 184, unify on (0).2 in 100 and (0).2.2 in 184
  have eq236 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq171 eq203 -- forward demodulation 203,171
  have eq237 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq236 eq179 -- backward demodulation 179,236
  have eq240 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ X2) = (X4 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq237 eq181 -- backward demodulation 181,237
  have eq245 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X0 ◇ X4)) := superpose eq240 eq174 -- backward demodulation 174,240
  have eq248 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X2 ◇ X0)) := superpose eq240 eq207 -- forward demodulation 207,240
  have eq250 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X1)) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq171 eq210 -- forward demodulation 210,171
  have eq251 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq100 eq250 -- forward demodulation 250,100
  have eq252 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq251 eq176 -- backward demodulation 176,251
  have eq263 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ X0) := superpose eq252 eq248 -- backward demodulation 248,252
  have eq267 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ (X3 ◇ X2)) := superpose eq263 eq11 -- backward demodulation 11,263
  have eq280 (X0 X2 X3 X4 : G) : ((X2 ◇ X0) ◇ X3) = (((X2 ◇ X0) ◇ X3) ◇ (X0 ◇ X4)) := superpose eq263 eq245 -- backward demodulation 245,263
  have eq285 (X0 X2 X3 X4 : G) : (X3 ◇ X2) = ((X3 ◇ X2) ◇ (X0 ◇ X4)) := superpose eq263 eq280 -- forward demodulation 280,263
  have eq297 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq47 eq267 -- superposition 267,47, 47 into 267, unify on (0).2 in 47 and (0).2 in 267
  have eq427 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq297 eq297 -- superposition 297,297, 297 into 297, unify on (0).2 in 297 and (0).1 in 297
  have eq621 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X4 ◇ (X2 ◇ X3)) := superpose eq285 eq427 -- superposition 427,285, 285 into 427, unify on (0).2 in 285 and (0).1 in 427
  have eq680 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq427 eq96 -- superposition 96,427, 427 into 96, unify on (0).2 in 427 and (0).2 in 96
  subsumption eq680 eq621


@[equational_result]
theorem Equation3561_implies_Equation4558 (G : Type*) [Magma G] (h : Equation3561 G) : Equation4558 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq9 eq29 -- forward demodulation 29,9
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.2 in 28
  have eq51 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.2 in 9
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.1 in 15
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq46 eq93 -- forward demodulation 93,46
  have eq95 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq94 eq51 -- backward demodulation 51,94
  have eq98 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq94 eq24 -- backward demodulation 24,94
  have eq106 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) := superpose eq95 eq35 -- backward demodulation 35,95
  have eq108 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq95 eq94 -- backward demodulation 94,95
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq108 eq9 -- backward demodulation 9,108
  have eq123 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq108 eq106 -- backward demodulation 106,108
  have eq126 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK1) := superpose eq108 eq10 -- backward demodulation 10,108
  have eq143 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X2 ◇ (X0 ◇ X4)) := superpose eq116 eq98 -- forward demodulation 98,116
  have eq144 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (X4 ◇ X2) := superpose eq116 eq143 -- forward demodulation 143,116
  have eq145 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = (X4 ◇ X2) := superpose eq116 eq144 -- forward demodulation 144,116
  have eq146 (X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X1 ◇ X2) ◇ (X3 ◇ X4)) := superpose eq108 eq145 -- forward demodulation 145,108
  have eq178 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq116 eq116 -- superposition 116,116, 116 into 116, unify on (0).2 in 116 and (0).2.2 in 116
  have eq180 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ X3) := superpose eq108 eq178 -- forward demodulation 178,108
  have eq186 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq180 eq126 -- superposition 126,180, 180 into 126, unify on (0).2 in 180 and (0).1 in 126
  have eq255 (X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ X3) := superpose eq123 eq146 -- superposition 146,123, 123 into 146, unify on (0).2 in 123 and (0).2 in 146
  have eq317 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq255 eq186 -- superposition 186,255, 255 into 186, unify on (0).2 in 255 and (0).2 in 186
  subsumption eq317 rfl


@[equational_result]
theorem Equation3348_implies_Equation317 (G : Type*) [Magma G] (h : Equation3348 G) : Equation317 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq27 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq22 eq27 -- forward demodulation 27,22
  have eq34 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq28 eq10 -- superposition 10,28, 28 into 10, unify on (0).2 in 28 and (0).2 in 10
  have eq45 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq28 eq22 -- superposition 22,28, 28 into 22, unify on (0).2 in 28 and (0).2 in 22
  have eq79 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq45 eq45 -- superposition 45,45, 45 into 45, unify on (0).2 in 45 and (0).1 in 45
  have eq87 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ X0) := superpose eq45 eq34 -- superposition 34,45, 45 into 34, unify on (0).2 in 45 and (0).2 in 34
  subsumption eq87 eq79


@[equational_result]
theorem Equation3348_implies_Equation3277 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3277 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq26 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK3)) := superpose eq22 eq10 -- backward demodulation 10,22
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq22 eq28 -- forward demodulation 28,22
  have eq33 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq29 eq29 -- superposition 29,29, 29 into 29, unify on (0).2 in 29 and (0).2.2 in 29
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq22 -- superposition 22,29, 29 into 22, unify on (0).2 in 29 and (0).2 in 22
  have eq93 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK1) := superpose eq33 eq26 -- superposition 26,33, 33 into 26, unify on (0).2 in 33 and (0).2 in 26
  have eq104 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq46 eq46 -- superposition 46,46, 46 into 46, unify on (0).2 in 46 and (0).1 in 46
  have eq123 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ X0) := superpose eq46 eq93 -- superposition 93,46, 46 into 93, unify on (0).2 in 46 and (0).2 in 93
  subsumption eq123 eq104


@[equational_result]
theorem Equation3348_implies_Equation3954 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3954 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq15 -- backward demodulation 15,23
  have eq27 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq23 eq10 -- backward demodulation 10,23
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq30 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq29 -- forward demodulation 29,23
  have eq48 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq30 eq23 -- superposition 23,30, 30 into 23, unify on (0).2 in 30 and (0).2 in 23
  have eq61 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq48 eq48 -- superposition 48,48, 48 into 48, unify on (0).2 in 48 and (0).1 in 48
  have eq74 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ X0) := superpose eq48 eq27 -- superposition 27,48, 48 into 27, unify on (0).2 in 48 and (0).2 in 27
  subsumption eq74 eq61


@[equational_result]
theorem Equation3348_implies_Equation362 (G : Type*) [Magma G] (h : Equation3348 G) : Equation362 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq15 -- backward demodulation 15,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq28 -- forward demodulation 28,23
  have eq45 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq23 -- superposition 23,29, 29 into 23, unify on (0).2 in 29 and (0).2 in 23
  have eq58 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq45 eq45 -- superposition 45,45, 45 into 45, unify on (0).2 in 45 and (0).1 in 45
  have eq71 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ X0) := superpose eq45 eq10 -- superposition 10,45, 45 into 10, unify on (0).2 in 45 and (0).2 in 10
  subsumption eq71 eq58


@[equational_result]
theorem Equation3348_implies_Equation3918 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3918 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = ((X1 ◇ X0) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq16 -- backward demodulation 16,23
  have eq27 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq23 eq10 -- backward demodulation 10,23
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X0) ◇ X3) := superpose eq13 eq24 -- forward demodulation 24,13
  subsumption eq27 eq28


@[equational_result]
theorem Equation3348_implies_Equation3370 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3370 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq26 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq22 eq10 -- backward demodulation 10,22
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq22 eq28 -- forward demodulation 28,22
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq29 eq22 -- superposition 22,29, 29 into 22, unify on (0).2 in 29 and (0).2 in 22
  have eq51 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq22 eq26 -- superposition 26,22, 22 into 26, unify on (0).2 in 22 and (0).2 in 26
  subsumption eq51 eq46


@[equational_result]
theorem Equation3348_implies_Equation4291 (G : Type*) [Magma G] (h : Equation3348 G) : Equation4291 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq22 eq15 -- backward demodulation 15,22
  have eq26 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq22 eq10 -- backward demodulation 10,22
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq22 eq28 -- forward demodulation 28,22
  subsumption eq26 eq29


@[equational_result]
theorem Equation3348_implies_Equation3951 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3951 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq25 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X3) := superpose eq23 eq15 -- backward demodulation 15,23
  have eq27 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq23 eq10 -- backward demodulation 10,23
  have eq29 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq30 (X0 X1 X3 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq23 eq29 -- forward demodulation 29,23
  have eq31 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq13 eq27 -- forward demodulation 27,13
  have eq48 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq30 eq23 -- superposition 23,30, 30 into 23, unify on (0).2 in 30 and (0).2 in 23
  have eq61 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq48 eq48 -- superposition 48,48, 48 into 48, unify on (0).2 in 48 and (0).1 in 48
  have eq80 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq48 eq31 -- superposition 31,48, 48 into 31, unify on (0).2 in 48 and (0).1 in 31
  subsumption eq80 eq61


