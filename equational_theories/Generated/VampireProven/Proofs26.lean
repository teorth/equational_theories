import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation3940_implies_Equation4143 (G : Type*) [Magma G] (h : Equation3940 G) : Equation4143 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) = ((X0 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.1 in 9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2 in 21
  have eq59 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ X2) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq12 eq21 -- superposition 21,12, 12 into 21, unify on (0).2 in 12 and (0).2 in 21
  have eq164 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq58 eq9 -- superposition 9,58, 58 into 9, unify on (0).2 in 58 and (0).2.1 in 9
  have eq251 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK2) := superpose eq164 eq10 -- backward demodulation 10,164
  have eq511 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = (X0 ◇ (X1 ◇ X2)) := superpose eq11 eq59 -- superposition 59,11, 11 into 59, unify on (0).2 in 11 and (0).2 in 59
  have eq734 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK2) := superpose eq511 eq251 -- backward demodulation 251,511
  subsumption eq734 eq9


@[equational_result]
theorem Equation2666_implies_Equation2062 (G : Type*) [Magma G] (h : Equation2666 G) : Equation2062 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X0) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq22 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq35 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq22 eq22 -- superposition 22,22, 22 into 22, unify on (0).2 in 22 and (0).1.1 in 22
  have eq36 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq35 eq22 -- superposition 22,35, 35 into 22, unify on (0).2 in 35 and (0).1.1 in 22
  have eq37 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq18 eq36 -- forward demodulation 36,18
  have eq105 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq18 eq22 -- superposition 22,18, 18 into 22, unify on (0).2 in 18 and (0).1.1 in 22
  have eq189 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose eq37 eq22 -- superposition 22,37, 37 into 22, unify on (0).2 in 37 and (0).1.1.1 in 22
  have eq202 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK2)) := superpose eq189 eq10 -- backward demodulation 10,189
  subsumption eq202 eq105


@[equational_result]
theorem Equation2666_implies_Equation3257 (G : Type*) [Magma G] (h : Equation2666 G) : Equation3257 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X0) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq22 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq23 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) ◇ X1) := superpose eq18 eq11 -- backward demodulation 11,18
  have eq38 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq22 eq23 -- superposition 23,22, 22 into 23, unify on (0).2 in 22 and (0).1 in 23
  have eq42 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq18 eq38 -- forward demodulation 38,18
  have eq81 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) = ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) := superpose eq22 eq18 -- superposition 18,22, 22 into 18, unify on (0).2 in 22 and (0).1.1 in 18
  have eq99 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq18 eq22 -- superposition 22,18, 18 into 22, unify on (0).2 in 18 and (0).1.1 in 22
  have eq109 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq18 eq22 -- superposition 22,18, 18 into 22, unify on (0).2 in 18 and (0).1.1.1 in 22
  have eq110 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) := superpose eq18 eq81 -- forward demodulation 81,18
  have eq111 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) := superpose eq22 eq110 -- forward demodulation 110,22
  have eq159 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := superpose eq22 eq99 -- superposition 99,22, 22 into 99, unify on (0).2 in 22 and (0).1.2 in 99
  have eq168 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq99 eq18 -- superposition 18,99, 99 into 18, unify on (0).2 in 99 and (0).1.1 in 18
  have eq169 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq109 eq159 -- forward demodulation 159,109
  have eq181 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq18 eq168 -- forward demodulation 168,18
  have eq182 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq169 eq181 -- forward demodulation 181,169
  have eq183 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) := superpose eq42 eq182 -- forward demodulation 182,42
  have eq184 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq111 eq183 -- forward demodulation 183,111
  have eq219 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq184 eq10 -- superposition 10,184, 184 into 10, unify on (0).2 in 184 and (0).2 in 10
  subsumption eq219 rfl


@[equational_result]
theorem Equation2666_implies_Equation4282 (G : Type*) [Magma G] (h : Equation2666 G) : Equation4282 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X0) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq22 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq23 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) ◇ X1) := superpose eq18 eq11 -- backward demodulation 11,18
  have eq38 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq22 eq23 -- superposition 23,22, 22 into 23, unify on (0).2 in 22 and (0).1 in 23
  have eq42 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq18 eq38 -- forward demodulation 38,18
  have eq81 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) = ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) := superpose eq22 eq18 -- superposition 18,22, 22 into 18, unify on (0).2 in 22 and (0).1.1 in 18
  have eq99 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq18 eq22 -- superposition 22,18, 18 into 22, unify on (0).2 in 18 and (0).1.1 in 22
  have eq109 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq18 eq22 -- superposition 22,18, 18 into 22, unify on (0).2 in 18 and (0).1.1.1 in 22
  have eq110 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) := superpose eq18 eq81 -- forward demodulation 81,18
  have eq111 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) := superpose eq22 eq110 -- forward demodulation 110,22
  have eq159 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := superpose eq22 eq99 -- superposition 99,22, 22 into 99, unify on (0).2 in 22 and (0).1.2 in 99
  have eq168 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq99 eq18 -- superposition 18,99, 99 into 18, unify on (0).2 in 99 and (0).1.1 in 18
  have eq169 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq109 eq159 -- forward demodulation 159,109
  have eq181 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq18 eq168 -- forward demodulation 168,18
  have eq182 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq169 eq181 -- forward demodulation 181,169
  have eq183 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) := superpose eq42 eq182 -- forward demodulation 182,42
  have eq184 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq111 eq183 -- forward demodulation 183,111
  have eq185 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ sK0) := superpose eq184 eq10 -- backward demodulation 10,184
  subsumption eq185 eq184


@[equational_result]
theorem Equation2666_implies_Equation3254 (G : Type*) [Magma G] (h : Equation2666 G) : Equation3254 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X0) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq22 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq23 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) ◇ X1) := superpose eq18 eq11 -- backward demodulation 11,18
  have eq35 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq22 eq22 -- superposition 22,22, 22 into 22, unify on (0).2 in 22 and (0).1.1 in 22
  have eq38 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq22 eq23 -- superposition 23,22, 22 into 23, unify on (0).2 in 22 and (0).1 in 23
  have eq42 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq18 eq38 -- forward demodulation 38,18
  have eq81 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) = ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) := superpose eq22 eq18 -- superposition 18,22, 22 into 18, unify on (0).2 in 22 and (0).1.1 in 18
  have eq99 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq18 eq22 -- superposition 22,18, 18 into 22, unify on (0).2 in 18 and (0).1.1 in 22
  have eq109 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq18 eq22 -- superposition 22,18, 18 into 22, unify on (0).2 in 18 and (0).1.1.1 in 22
  have eq110 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) := superpose eq18 eq81 -- forward demodulation 81,18
  have eq111 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) := superpose eq22 eq110 -- forward demodulation 110,22
  have eq159 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := superpose eq22 eq99 -- superposition 99,22, 22 into 99, unify on (0).2 in 22 and (0).1.2 in 99
  have eq168 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq99 eq18 -- superposition 18,99, 99 into 18, unify on (0).2 in 99 and (0).1.1 in 18
  have eq169 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq109 eq159 -- forward demodulation 159,109
  have eq181 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq18 eq168 -- forward demodulation 168,18
  have eq182 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq169 eq181 -- forward demodulation 181,169
  have eq183 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) := superpose eq42 eq182 -- forward demodulation 182,42
  have eq184 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq111 eq183 -- forward demodulation 183,111
  have eq185 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq184 eq10 -- backward demodulation 10,184
  subsumption eq185 eq35


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
theorem Equation2666_implies_Equation3458 (G : Type*) [Magma G] (h : Equation2666 G) : Equation3458 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X0) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq22 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq99 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq18 eq22 -- superposition 22,18, 18 into 22, unify on (0).2 in 18 and (0).1.1 in 22
  have eq109 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq18 eq22 -- superposition 22,18, 18 into 22, unify on (0).2 in 18 and (0).1.1.1 in 22
  have eq158 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq22 eq99 -- superposition 99,22, 22 into 99, unify on (0).2 in 22 and (0).1.1 in 99
  have eq159 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := superpose eq22 eq99 -- superposition 99,22, 22 into 99, unify on (0).2 in 22 and (0).1.2 in 99
  have eq169 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq109 eq159 -- forward demodulation 159,109
  have eq170 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := superpose eq169 eq10 -- backward demodulation 10,169
  subsumption eq170 eq158


@[equational_result]
theorem Equation2666_implies_Equation308 (G : Type*) [Magma G] (h : Equation2666 G) : Equation308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X0) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq22 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq23 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) ◇ X1) := superpose eq18 eq11 -- backward demodulation 11,18
  have eq38 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq22 eq23 -- superposition 23,22, 22 into 23, unify on (0).2 in 22 and (0).1 in 23
  have eq42 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq18 eq38 -- forward demodulation 38,18
  have eq81 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) = ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) := superpose eq22 eq18 -- superposition 18,22, 22 into 18, unify on (0).2 in 22 and (0).1.1 in 18
  have eq99 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq18 eq22 -- superposition 22,18, 18 into 22, unify on (0).2 in 18 and (0).1.1 in 22
  have eq109 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq18 eq22 -- superposition 22,18, 18 into 22, unify on (0).2 in 18 and (0).1.1.1 in 22
  have eq110 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) := superpose eq18 eq81 -- forward demodulation 81,18
  have eq111 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) := superpose eq22 eq110 -- forward demodulation 110,22
  have eq159 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := superpose eq22 eq99 -- superposition 99,22, 22 into 99, unify on (0).2 in 22 and (0).1.2 in 99
  have eq168 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq99 eq18 -- superposition 18,99, 99 into 18, unify on (0).2 in 99 and (0).1.1 in 18
  have eq169 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq109 eq159 -- forward demodulation 159,109
  have eq181 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq18 eq168 -- forward demodulation 168,18
  have eq182 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq169 eq181 -- forward demodulation 181,169
  have eq183 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) := superpose eq42 eq182 -- forward demodulation 182,42
  have eq184 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq111 eq183 -- forward demodulation 183,111
  have eq213 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq184 eq10 -- superposition 10,184, 184 into 10, unify on (0).2 in 184 and (0).2 in 10
  subsumption eq213 rfl


@[equational_result]
theorem Equation2513_implies_Equation307 (G : Type*) [Magma G] (h : Equation2513 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1.1 in 11
  have eq18 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq9 -- backward demodulation 9,13
  subsumption eq18 eq13


@[equational_result]
theorem Equation2513_implies_Equation4380 (G : Type*) [Magma G] (h : Equation2513 G) : Equation4380 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq14 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1.1 in 11
  have eq19 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq13 -- backward demodulation 13,14
  subsumption eq19 eq14


@[equational_result]
theorem Equation2513_implies_Equation3715 (G : Type*) [Magma G] (h : Equation2513 G) : Equation3715 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq19 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq20 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq19 -- forward demodulation 19,14
  subsumption eq20 rfl


@[equational_result]
theorem Equation2513_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2513 G) : Equation2238 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1.1 in 11
  have eq18 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq13 eq9 -- backward demodulation 9,13
  have eq19 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq13 eq18 -- forward demodulation 18,13
  subsumption eq19 eq11


@[equational_result]
theorem Equation2513_implies_Equation4470 (G : Type*) [Magma G] (h : Equation2513 G) : Equation4470 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq19 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq20 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq19 -- forward demodulation 19,14
  subsumption eq20 rfl


@[equational_result]
theorem Equation2513_implies_Equation3149 (G : Type*) [Magma G] (h : Equation2513 G) : Equation3149 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation2513_implies_Equation3210 (G : Type*) [Magma G] (h : Equation2513 G) : Equation3210 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK2) ◇ sK2) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 : sK0 ≠ ((sK2 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation2513_implies_Equation4090 (G : Type*) [Magma G] (h : Equation2513 G) : Equation4090 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq23 : sK0 ≠ sK0 := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  subsumption eq23 rfl


@[equational_result]
theorem Equation138_implies_Equation3989 (G : Type*) [Magma G] (h : Equation138 G) : Equation3989 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq29 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation138_implies_Equation3915 (G : Type*) [Magma G] (h : Equation138 G) : Equation3915 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq29 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation138_implies_Equation2087 (G : Type*) [Magma G] (h : Equation138 G) : Equation2087 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation138_implies_Equation2203 (G : Type*) [Magma G] (h : Equation138 G) : Equation2203 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK2) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation138_implies_Equation2227 (G : Type*) [Magma G] (h : Equation138 G) : Equation2227 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK3) ◇ (sK3 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation138_implies_Equation2050 (G : Type*) [Magma G] (h : Equation138 G) : Equation2050 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation138_implies_Equation2115 (G : Type*) [Magma G] (h : Equation138 G) : Equation2115 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK2) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation138_implies_Equation159 (G : Type*) [Magma G] (h : Equation138 G) : Equation159 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq44 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq44 rfl


@[equational_result]
theorem Equation138_implies_Equation4023 (G : Type*) [Magma G] (h : Equation138 G) : Equation4023 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq29 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation1687_implies_Equation3862 (G : Type*) [Magma G] (h : Equation1687 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq26 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2.1 in 12
  have eq51 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).2 in 9
  subsumption eq51 rfl


@[equational_result]
theorem Equation1687_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1687 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq15 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X1 := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1 in 11
  have eq19 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1 in 8
  have eq26 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2.1 in 12
  have eq33 (X1 X3 : G) : ((X3 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq26 eq15 -- backward demodulation 15,26
  have eq38 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq26 eq19 -- backward demodulation 19,26
  have eq39 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq26 eq33 -- forward demodulation 33,26
  have eq41 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq11 eq38 -- forward demodulation 38,11
  have eq88 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq39 eq41 -- superposition 41,39, 39 into 41, unify on (0).2 in 39 and (0).2 in 41
  have eq104 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq88 eq9 -- backward demodulation 9,88
  subsumption eq104 eq88


@[equational_result]
theorem Equation1687_implies_Equation1022 (G : Type*) [Magma G] (h : Equation1687 G) : Equation1022 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq20 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq27 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq34 (X1 X3 : G) : ((X3 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq27 eq16 -- backward demodulation 16,27
  have eq39 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq27 eq10 -- backward demodulation 10,27
  have eq40 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq27 eq20 -- backward demodulation 20,27
  have eq41 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq27 eq34 -- forward demodulation 34,27
  have eq43 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq12 eq40 -- forward demodulation 40,12
  have eq90 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq41 eq43 -- superposition 43,41, 41 into 43, unify on (0).2 in 41 and (0).2 in 43
  have eq113 : sK0 ≠ sK0 := superpose eq90 eq39 -- superposition 39,90, 90 into 39, unify on (0).2 in 90 and (0).2 in 39
  subsumption eq113 rfl


@[equational_result]
theorem Equation1687_implies_Equation3253 (G : Type*) [Magma G] (h : Equation1687 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2.1 in 11
  have eq26 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2.1 in 12
  have eq34 (X1 : G) : (X1 ◇ X1) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq26 eq13 -- backward demodulation 13,26
  have eq75 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq34 eq9 -- superposition 9,34, 34 into 9, unify on (0).2 in 34 and (0).2 in 9
  subsumption eq75 rfl


@[equational_result]
theorem Equation1687_implies_Equation151 (G : Type*) [Magma G] (h : Equation1687 G) : Equation151 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq15 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X1 := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1 in 11
  have eq26 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2.1 in 12
  have eq33 (X1 X3 : G) : ((X3 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq26 eq15 -- backward demodulation 15,26
  have eq39 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq26 eq33 -- forward demodulation 33,26
  have eq66 : sK0 ≠ sK0 := superpose eq39 eq9 -- superposition 9,39, 39 into 9, unify on (0).2 in 39 and (0).2 in 9
  subsumption eq66 rfl


@[equational_result]
theorem Equation1687_implies_Equation3915 (G : Type*) [Magma G] (h : Equation1687 G) : Equation3915 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq20 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq27 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq34 (X1 X3 : G) : ((X3 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq27 eq16 -- backward demodulation 16,27
  have eq39 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq27 eq20 -- backward demodulation 20,27
  have eq40 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq27 eq34 -- forward demodulation 34,27
  have eq42 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq12 eq39 -- forward demodulation 39,12
  have eq89 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq40 eq42 -- superposition 42,40, 40 into 42, unify on (0).2 in 40 and (0).2 in 42
  have eq104 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq89 eq10 -- backward demodulation 10,89
  subsumption eq104 rfl


@[equational_result]
theorem Equation1687_implies_Equation3870 (G : Type*) [Magma G] (h : Equation1687 G) : Equation3870 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq27 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X2) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq52 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq27 eq10 -- superposition 10,27, 27 into 10, unify on (0).2 in 27 and (0).2 in 10
  subsumption eq52 rfl


@[equational_result]
theorem Equation1687_implies_Equation8 (G : Type*) [Magma G] (h : Equation1687 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq15 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X1 := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1 in 11
  have eq19 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1 in 8
  have eq26 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2.1 in 12
  have eq33 (X1 X3 : G) : ((X3 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq26 eq15 -- backward demodulation 15,26
  have eq38 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq26 eq19 -- backward demodulation 19,26
  have eq39 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq26 eq33 -- forward demodulation 33,26
  have eq41 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq11 eq38 -- forward demodulation 38,11
  have eq88 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq39 eq41 -- superposition 41,39, 39 into 41, unify on (0).2 in 39 and (0).2 in 41
  have eq128 : sK0 ≠ sK0 := superpose eq88 eq9 -- superposition 9,88, 88 into 9, unify on (0).2 in 88 and (0).2 in 9
  subsumption eq128 rfl


@[equational_result]
theorem Equation1687_implies_Equation1028 (G : Type*) [Magma G] (h : Equation1687 G) : Equation1028 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq20 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq27 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X2) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq34 (X1 X3 : G) : ((X3 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq27 eq16 -- backward demodulation 16,27
  have eq39 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq27 eq10 -- backward demodulation 10,27
  have eq40 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq27 eq20 -- backward demodulation 20,27
  have eq41 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq27 eq34 -- forward demodulation 34,27
  have eq43 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq12 eq40 -- forward demodulation 40,12
  have eq90 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq41 eq43 -- superposition 43,41, 41 into 43, unify on (0).2 in 41 and (0).2 in 43
  have eq113 : sK0 ≠ sK0 := superpose eq90 eq39 -- superposition 39,90, 90 into 39, unify on (0).2 in 90 and (0).2 in 39
  subsumption eq113 rfl


@[equational_result]
theorem Equation1687_implies_Equation2040 (G : Type*) [Magma G] (h : Equation1687 G) : Equation2040 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq27 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq34 (X1 X3 : G) : ((X3 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq27 eq16 -- backward demodulation 16,27
  have eq40 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq27 eq34 -- forward demodulation 34,27
  have eq51 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq27 eq10 -- superposition 10,27, 27 into 10, unify on (0).2 in 27 and (0).2 in 10
  subsumption eq51 eq40


@[equational_result]
theorem Equation1687_implies_Equation1228 (G : Type*) [Magma G] (h : Equation1687 G) : Equation1228 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq20 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq27 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq34 (X1 X3 : G) : ((X3 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq27 eq16 -- backward demodulation 16,27
  have eq39 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq27 eq20 -- backward demodulation 20,27
  have eq40 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := superpose eq27 eq10 -- backward demodulation 10,27
  have eq41 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq27 eq34 -- forward demodulation 34,27
  have eq43 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq12 eq39 -- forward demodulation 39,12
  have eq44 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq27 eq40 -- forward demodulation 40,27
  have eq91 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq41 eq43 -- superposition 43,41, 41 into 43, unify on (0).2 in 41 and (0).2 in 43
  have eq114 : sK0 ≠ sK0 := superpose eq91 eq44 -- superposition 44,91, 91 into 44, unify on (0).2 in 91 and (0).2 in 44
  subsumption eq114 rfl


@[equational_result]
theorem Equation1687_implies_Equation1035 (G : Type*) [Magma G] (h : Equation1687 G) : Equation1035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq20 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq27 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq34 (X1 X3 : G) : ((X3 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq27 eq16 -- backward demodulation 16,27
  have eq36 (X0 X2 : G) : (X0 ◇ X0) = ((X2 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq27 eq13 -- backward demodulation 13,27
  have eq39 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq27 eq20 -- backward demodulation 20,27
  have eq40 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq27 eq34 -- forward demodulation 34,27
  have eq41 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq36 eq10 -- backward demodulation 10,36
  have eq43 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq12 eq39 -- forward demodulation 39,12
  have eq90 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq40 eq43 -- superposition 43,40, 40 into 43, unify on (0).2 in 40 and (0).2 in 43
  have eq113 : sK0 ≠ sK0 := superpose eq90 eq41 -- superposition 41,90, 90 into 41, unify on (0).2 in 90 and (0).2 in 41
  subsumption eq113 rfl


@[equational_result]
theorem Equation1687_implies_Equation3864 (G : Type*) [Magma G] (h : Equation1687 G) : Equation3864 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq27 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq52 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq27 eq10 -- superposition 10,27, 27 into 10, unify on (0).2 in 27 and (0).2 in 10
  subsumption eq52 rfl


@[equational_result]
theorem Equation1687_implies_Equation99 (G : Type*) [Magma G] (h : Equation1687 G) : Equation99 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq15 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X1 := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1 in 11
  have eq19 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1 in 8
  have eq26 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2.1 in 12
  have eq33 (X1 X3 : G) : ((X3 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq26 eq15 -- backward demodulation 15,26
  have eq38 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq26 eq9 -- backward demodulation 9,26
  have eq39 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq26 eq19 -- backward demodulation 19,26
  have eq40 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq26 eq33 -- forward demodulation 33,26
  have eq42 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq11 eq39 -- forward demodulation 39,11
  have eq89 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq40 eq42 -- superposition 42,40, 40 into 42, unify on (0).2 in 40 and (0).2 in 42
  have eq109 : sK0 ≠ sK0 := superpose eq89 eq38 -- superposition 38,89, 89 into 38, unify on (0).2 in 89 and (0).2 in 38
  subsumption eq109 rfl


@[equational_result]
theorem Equation1687_implies_Equation1025 (G : Type*) [Magma G] (h : Equation1687 G) : Equation1025 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq20 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq27 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq34 (X1 X3 : G) : ((X3 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq27 eq16 -- backward demodulation 16,27
  have eq39 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq27 eq10 -- backward demodulation 10,27
  have eq40 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq27 eq20 -- backward demodulation 20,27
  have eq41 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq27 eq34 -- forward demodulation 34,27
  have eq43 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq12 eq40 -- forward demodulation 40,12
  have eq90 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq41 eq43 -- superposition 43,41, 41 into 43, unify on (0).2 in 41 and (0).2 in 43
  have eq113 : sK0 ≠ sK0 := superpose eq90 eq39 -- superposition 39,90, 90 into 39, unify on (0).2 in 90 and (0).2 in 39
  subsumption eq113 rfl


@[equational_result]
theorem Equation1687_implies_Equation2035 (G : Type*) [Magma G] (h : Equation1687 G) : Equation2035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq15 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X1 := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1 in 11
  have eq26 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2.1 in 12
  have eq33 (X1 X3 : G) : ((X3 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq26 eq15 -- backward demodulation 15,26
  have eq39 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq26 eq9 -- backward demodulation 9,26
  have eq40 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq26 eq33 -- forward demodulation 33,26
  subsumption eq39 eq40


@[equational_result]
theorem Equation1687_implies_Equation3873 (G : Type*) [Magma G] (h : Equation1687 G) : Equation3873 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq27 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq52 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq27 eq10 -- superposition 10,27, 27 into 10, unify on (0).2 in 27 and (0).2 in 10
  subsumption eq52 rfl


@[equational_result]
theorem Equation1687_implies_Equation3877 (G : Type*) [Magma G] (h : Equation1687 G) : Equation3877 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq27 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq36 (X0 X2 : G) : (X0 ◇ X0) = ((X2 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq27 eq13 -- backward demodulation 13,27
  have eq57 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq36 eq10 -- superposition 10,36, 36 into 10, unify on (0).2 in 36 and (0).2 in 10
  subsumption eq57 rfl


@[equational_result]
theorem Equation1687_implies_Equation1031 (G : Type*) [Magma G] (h : Equation1687 G) : Equation1031 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq20 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq27 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq34 (X1 X3 : G) : ((X3 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq27 eq16 -- backward demodulation 16,27
  have eq39 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq27 eq10 -- backward demodulation 10,27
  have eq40 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq27 eq20 -- backward demodulation 20,27
  have eq41 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq27 eq34 -- forward demodulation 34,27
  have eq43 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq12 eq40 -- forward demodulation 40,12
  have eq90 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq41 eq43 -- superposition 43,41, 41 into 43, unify on (0).2 in 41 and (0).2 in 43
  have eq113 : sK0 ≠ sK0 := superpose eq90 eq39 -- superposition 39,90, 90 into 39, unify on (0).2 in 90 and (0).2 in 39
  subsumption eq113 rfl


@[equational_result]
theorem Equation1687_implies_Equation4065 (G : Type*) [Magma G] (h : Equation1687 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq26 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2.1 in 12
  have eq39 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq26 eq9 -- backward demodulation 9,26
  subsumption eq39 eq26


@[equational_result]
theorem Equation1687_implies_Equation4070 (G : Type*) [Magma G] (h : Equation1687 G) : Equation4070 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq27 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq40 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq27 eq10 -- backward demodulation 10,27
  subsumption eq40 eq27


@[equational_result]
theorem Equation1687_implies_Equation3316 (G : Type*) [Magma G] (h : Equation1687 G) : Equation3316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq20 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq27 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq34 (X1 X3 : G) : ((X3 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq27 eq16 -- backward demodulation 16,27
  have eq39 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq27 eq20 -- backward demodulation 20,27
  have eq40 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq27 eq34 -- forward demodulation 34,27
  have eq42 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq12 eq39 -- forward demodulation 39,12
  have eq49 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq27 eq27 -- superposition 27,27, 27 into 27, unify on (0).2 in 27 and (0).1.1 in 27
  have eq174 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq49 eq49 -- superposition 49,49, 49 into 49, unify on (0).2 in 49 and (0).1.1 in 49
  have eq201 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq42 eq174 -- forward demodulation 174,42
  have eq202 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq40 eq201 -- forward demodulation 201,40
  have eq203 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq202 -- forward demodulation 202,12
  have eq257 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq203 eq10 -- superposition 10,203, 203 into 10, unify on (0).2 in 203 and (0).2 in 10
  subsumption eq257 rfl


@[equational_result]
theorem Equation1687_implies_Equation2124 (G : Type*) [Magma G] (h : Equation1687 G) : Equation2124 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq27 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X2) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq34 (X1 X3 : G) : ((X3 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq27 eq16 -- backward demodulation 16,27
  have eq40 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq27 eq34 -- forward demodulation 34,27
  have eq67 : sK0 ≠ sK0 := superpose eq40 eq10 -- superposition 10,40, 40 into 10, unify on (0).2 in 40 and (0).2 in 10
  subsumption eq67 rfl


@[equational_result]
theorem Equation1687_implies_Equation2087 (G : Type*) [Magma G] (h : Equation1687 G) : Equation2087 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq27 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq34 (X1 X3 : G) : ((X3 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq27 eq16 -- backward demodulation 16,27
  have eq40 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq27 eq34 -- forward demodulation 34,27
  have eq67 : sK0 ≠ sK0 := superpose eq40 eq10 -- superposition 10,40, 40 into 10, unify on (0).2 in 40 and (0).2 in 10
  subsumption eq67 rfl


@[equational_result]
theorem Equation1687_implies_Equation2050 (G : Type*) [Magma G] (h : Equation1687 G) : Equation2050 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq27 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq34 (X1 X3 : G) : ((X3 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq27 eq16 -- backward demodulation 16,27
  have eq40 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq27 eq10 -- backward demodulation 10,27
  have eq41 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq27 eq34 -- forward demodulation 34,27
  subsumption eq40 eq41


@[equational_result]
theorem Equation1687_implies_Equation1894 (G : Type*) [Magma G] (h : Equation1687 G) : Equation1894 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq20 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq27 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq34 (X1 X3 : G) : ((X3 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq27 eq16 -- backward demodulation 16,27
  have eq39 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq27 eq20 -- backward demodulation 20,27
  have eq40 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq27 eq34 -- forward demodulation 34,27
  have eq42 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq12 eq39 -- forward demodulation 39,12
  have eq49 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq27 eq27 -- superposition 27,27, 27 into 27, unify on (0).2 in 27 and (0).1.1 in 27
  have eq175 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq27 eq49 -- superposition 49,27, 27 into 49, unify on (0).2 in 27 and (0).1.1 in 49
  have eq204 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq42 eq175 -- forward demodulation 175,42
  have eq205 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq40 eq204 -- forward demodulation 204,40
  have eq296 : sK0 ≠ sK0 := superpose eq205 eq10 -- superposition 10,205, 205 into 10, unify on (0).2 in 205 and (0).2 in 10
  subsumption eq296 rfl


@[equational_result]
theorem Equation1687_implies_Equation359 (G : Type*) [Magma G] (h : Equation1687 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq26 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2.1 in 12
  have eq53 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).2 in 9
  subsumption eq53 rfl


@[equational_result]
theorem Equation1687_implies_Equation4631 (G : Type*) [Magma G] (h : Equation1687 G) : Equation4631 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK2) ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq27 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq39 : ((sK0 ◇ sK2) ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq27 eq10 -- backward demodulation 10,27
  subsumption eq39 eq27


@[equational_result]
theorem Equation1687_implies_Equation361 (G : Type*) [Magma G] (h : Equation1687 G) : Equation361 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq27 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq52 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq27 eq10 -- superposition 10,27, 27 into 10, unify on (0).2 in 27 and (0).2 in 10
  subsumption eq52 rfl


@[equational_result]
theorem Equation1687_implies_Equation2161 (G : Type*) [Magma G] (h : Equation1687 G) : Equation2161 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq27 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq34 (X1 X3 : G) : ((X3 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq27 eq16 -- backward demodulation 16,27
  have eq40 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq27 eq34 -- forward demodulation 34,27
  have eq67 : sK0 ≠ sK0 := superpose eq40 eq10 -- superposition 10,40, 40 into 10, unify on (0).2 in 40 and (0).2 in 10
  subsumption eq67 rfl


@[equational_result]
theorem Equation418_implies_Equation203 (G : Type*) [Magma G] (h : Equation418 G) : Equation203 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2 in 13
  subsumption eq17 rfl


@[equational_result]
theorem Equation418_implies_Equation616 (G : Type*) [Magma G] (h : Equation418 G) : Equation616 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X3 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation418_implies_Equation622 (G : Type*) [Magma G] (h : Equation418 G) : Equation622 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X3 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq11


@[equational_result]
theorem Equation418_implies_Equation413 (G : Type*) [Magma G] (h : Equation418 G) : Equation413 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X3 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation418_implies_Equation619 (G : Type*) [Magma G] (h : Equation418 G) : Equation619 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X3 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation418_implies_Equation23 (G : Type*) [Magma G] (h : Equation418 G) : Equation23 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq9 -- backward demodulation 9,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation418_implies_Equation625 (G : Type*) [Magma G] (h : Equation418 G) : Equation625 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X3 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq23 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq23 rfl


@[equational_result]
theorem Equation418_implies_Equation1428 (G : Type*) [Magma G] (h : Equation418 G) : Equation1428 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X3 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq11


@[equational_result]
theorem Equation418_implies_Equation2243 (G : Type*) [Magma G] (h : Equation418 G) : Equation2243 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X3 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation418_implies_Equation3255 (G : Type*) [Magma G] (h : Equation418 G) : Equation3255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X3 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation418_implies_Equation2847 (G : Type*) [Magma G] (h : Equation418 G) : Equation2847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq15 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq13 -- backward demodulation 13,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation418_implies_Equation3050 (G : Type*) [Magma G] (h : Equation418 G) : Equation3050 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq14 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation418_implies_Equation4380 (G : Type*) [Magma G] (h : Equation418 G) : Equation4380 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq15 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq13 -- backward demodulation 13,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation418_implies_Equation819 (G : Type*) [Magma G] (h : Equation418 G) : Equation819 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X3 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq11


@[equational_result]
theorem Equation418_implies_Equation414 (G : Type*) [Magma G] (h : Equation418 G) : Equation414 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq17 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq37 : sK0 ≠ sK0 := superpose eq17 eq15 -- superposition 15,17, 17 into 15, unify on (0).2 in 17 and (0).2 in 15
  subsumption eq37 rfl


@[equational_result]
theorem Equation418_implies_Equation415 (G : Type*) [Magma G] (h : Equation418 G) : Equation415 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq32 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq32 rfl


@[equational_result]
theorem Equation2113_implies_Equation1334 (G : Type*) [Magma G] (h : Equation2113 G) : Equation1334 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq33 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq44 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).2.1 in 30
  have eq45 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ X1) = ((X2 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq11 eq30 -- superposition 30,11, 11 into 30, unify on (0).2 in 11 and (0).2.1 in 30
  have eq49 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq30 eq9 -- superposition 9,30, 30 into 9, unify on (0).2 in 30 and (0).1.1 in 9
  have eq57 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq44 eq33 -- backward demodulation 33,44
  have eq87 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2))) := superpose eq45 eq10 -- backward demodulation 10,45
  have eq98 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq49 eq87 -- backward demodulation 87,49
  subsumption eq98 eq57


@[equational_result]
theorem Equation2113_implies_Equation1682 (G : Type*) [Magma G] (h : Equation2113 G) : Equation1682 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X3))) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = (X3 ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.2 in 12
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq33 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq44 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).2.1 in 30
  have eq57 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq44 eq33 -- backward demodulation 33,44
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq44 eq17 -- backward demodulation 17,44
  have eq60 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X3))) = X3 := superpose eq58 eq15 -- backward demodulation 15,58
  have eq125 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq57 eq30 -- superposition 30,57, 57 into 30, unify on (0).2 in 57 and (0).2.1 in 30
  have eq132 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq125 eq10 -- backward demodulation 10,125
  have eq133 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq125 eq132 -- forward demodulation 132,125
  subsumption eq133 eq60


@[equational_result]
theorem Equation2113_implies_Equation2079 (G : Type*) [Magma G] (h : Equation2113 G) : Equation2079 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X3))) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = (X3 ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.2 in 12
  have eq18 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ X2) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq33 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq44 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).2.1 in 30
  have eq57 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq44 eq33 -- backward demodulation 33,44
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq44 eq17 -- backward demodulation 17,44
  have eq60 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X3))) = X3 := superpose eq58 eq15 -- backward demodulation 15,58
  have eq61 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ (X0 ◇ X2)) ◇ X2) = X3 := superpose eq58 eq18 -- backward demodulation 18,58
  have eq68 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X3 := superpose eq58 eq61 -- forward demodulation 61,58
  have eq123 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq57 eq30 -- superposition 30,57, 57 into 30, unify on (0).2 in 57 and (0).2.1 in 30
  have eq131 : sK0 ≠ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK1)) := superpose eq123 eq10 -- backward demodulation 10,123
  have eq132 : sK0 ≠ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) := superpose eq123 eq131 -- forward demodulation 131,123
  have eq243 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X2)) := superpose eq60 eq30 -- superposition 30,60, 60 into 30, unify on (0).2 in 60 and (0).2.1 in 30
  have eq277 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK2)) := superpose eq243 eq132 -- backward demodulation 132,243
  have eq297 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK2) := superpose eq58 eq277 -- superposition 277,58, 58 into 277, unify on (0).2 in 58 and (0).2 in 277
  subsumption eq297 eq68


@[equational_result]
theorem Equation2113_implies_Equation2132 (G : Type*) [Magma G] (h : Equation2113 G) : Equation2132 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X3))) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = (X3 ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.2 in 12
  have eq19 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ (X0 ◇ X3)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq33 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq40 (X1 X3 : G) : ((X3 ◇ X1) ◇ X3) = X1 := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).1 in 30
  have eq44 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).2.1 in 30
  have eq45 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ X1) = ((X2 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq11 eq30 -- superposition 30,11, 11 into 30, unify on (0).2 in 11 and (0).2.1 in 30
  have eq49 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq30 eq9 -- superposition 9,30, 30 into 9, unify on (0).2 in 30 and (0).1.1 in 9
  have eq56 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X1 ◇ X2))) = X0 := superpose eq30 eq12 -- superposition 12,30, 30 into 12, unify on (0).2 in 30 and (0).1.2.2 in 12
  have eq57 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq44 eq33 -- backward demodulation 33,44
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq44 eq17 -- backward demodulation 17,44
  have eq60 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X3))) = X3 := superpose eq58 eq15 -- backward demodulation 15,58
  have eq62 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X2 ◇ X3) ◇ (X0 ◇ X3)) := superpose eq58 eq19 -- backward demodulation 19,58
  have eq75 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ X3) ◇ ((X0 ◇ X2) ◇ (X1 ◇ X3))) := superpose eq45 eq11 -- backward demodulation 11,45
  have eq102 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) = X0 := superpose eq45 eq56 -- forward demodulation 56,45
  have eq103 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq49 eq102 -- forward demodulation 102,49
  have eq113 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq75 -- superposition 75,9, 9 into 75, unify on (0).2 in 9 and (0).2.2 in 75
  have eq119 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK2 ◇ sK2)) := superpose eq113 eq10 -- backward demodulation 10,113
  have eq120 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq40 eq119 -- forward demodulation 119,40
  have eq235 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq57 eq60 -- superposition 60,57, 57 into 60, unify on (0).2 in 57 and (0).1.2 in 60
  have eq312 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq58 eq62 -- superposition 62,58, 58 into 62, unify on (0).2 in 58 and (0).2 in 62
  have eq456 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq103 eq235 -- superposition 235,103, 103 into 235, unify on (0).2 in 103 and (0).1 in 235
  have eq588 (X0 : G) : sK0 ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq312 eq120 -- superposition 120,312, 312 into 120, unify on (0).2 in 312 and (0).2.2 in 120
  subsumption eq588 eq456


@[equational_result]
theorem Equation2113_implies_Equation2146 (G : Type*) [Magma G] (h : Equation2113 G) : Equation2146 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK2) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X3))) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = (X3 ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.2 in 12
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq33 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq44 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).2.1 in 30
  have eq45 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ X1) = ((X2 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq11 eq30 -- superposition 30,11, 11 into 30, unify on (0).2 in 11 and (0).2.1 in 30
  have eq49 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq30 eq9 -- superposition 9,30, 30 into 9, unify on (0).2 in 30 and (0).1.1 in 9
  have eq55 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X1 ◇ X2))) = X0 := superpose eq30 eq12 -- superposition 12,30, 30 into 12, unify on (0).2 in 30 and (0).1.2.2 in 12
  have eq57 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq44 eq33 -- backward demodulation 33,44
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq44 eq17 -- backward demodulation 17,44
  have eq60 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X3))) = X3 := superpose eq58 eq15 -- backward demodulation 15,58
  have eq101 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) = X0 := superpose eq45 eq55 -- forward demodulation 55,45
  have eq102 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq49 eq101 -- forward demodulation 101,49
  have eq123 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq57 eq30 -- superposition 30,57, 57 into 30, unify on (0).2 in 57 and (0).2.1 in 30
  have eq131 : sK0 ≠ ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK2)) := superpose eq123 eq10 -- backward demodulation 10,123
  have eq242 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X2)) := superpose eq60 eq30 -- superposition 30,60, 60 into 30, unify on (0).2 in 60 and (0).2.1 in 30
  have eq276 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK2)) := superpose eq242 eq131 -- backward demodulation 131,242
  have eq277 : sK0 ≠ (sK2 ◇ (sK0 ◇ sK2)) := superpose eq57 eq276 -- forward demodulation 276,57
  subsumption eq277 eq102


@[equational_result]
theorem Equation2113_implies_Equation481 (G : Type*) [Magma G] (h : Equation2113 G) : Equation481 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X3))) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = (X3 ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.2 in 12
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq33 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq44 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).2.1 in 30
  have eq45 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ X1) = ((X2 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq11 eq30 -- superposition 30,11, 11 into 30, unify on (0).2 in 11 and (0).2.1 in 30
  have eq49 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq30 eq9 -- superposition 9,30, 30 into 9, unify on (0).2 in 30 and (0).1.1 in 9
  have eq56 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X1 ◇ X2))) = X0 := superpose eq30 eq12 -- superposition 12,30, 30 into 12, unify on (0).2 in 30 and (0).1.2.2 in 12
  have eq57 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq44 eq33 -- backward demodulation 33,44
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq44 eq17 -- backward demodulation 17,44
  have eq60 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X3))) = X3 := superpose eq58 eq15 -- backward demodulation 15,58
  have eq102 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) = X0 := superpose eq45 eq56 -- forward demodulation 56,45
  have eq103 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq49 eq102 -- forward demodulation 102,49
  have eq247 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq57 eq60 -- superposition 60,57, 57 into 60, unify on (0).2 in 57 and (0).1.2 in 60
  have eq400 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq103 eq247 -- superposition 247,103, 103 into 247, unify on (0).2 in 103 and (0).1 in 247
  have eq421 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq400 eq10 -- backward demodulation 10,400
  subsumption eq421 eq103


@[equational_result]
theorem Equation2113_implies_Equation2669 (G : Type*) [Magma G] (h : Equation2113 G) : Equation2669 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = (X3 ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.2 in 12
  have eq18 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ X2) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq19 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ (X0 ◇ X3)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq33 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq44 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).2.1 in 30
  have eq57 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq44 eq33 -- backward demodulation 33,44
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq44 eq17 -- backward demodulation 17,44
  have eq61 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ (X0 ◇ X2)) ◇ X2) = X3 := superpose eq58 eq18 -- backward demodulation 18,58
  have eq62 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X2 ◇ X3) ◇ (X0 ◇ X3)) := superpose eq58 eq19 -- backward demodulation 19,58
  have eq68 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X3 := superpose eq58 eq61 -- forward demodulation 61,58
  have eq123 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq57 eq30 -- superposition 30,57, 57 into 30, unify on (0).2 in 57 and (0).2.1 in 30
  have eq131 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq123 eq10 -- backward demodulation 10,123
  have eq132 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq62 eq131 -- forward demodulation 131,62
  subsumption eq132 eq68


@[equational_result]
theorem Equation2113_implies_Equation1885 (G : Type*) [Magma G] (h : Equation2113 G) : Equation1885 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X3))) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = (X3 ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.2 in 12
  have eq18 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ X2) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq44 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).2.1 in 30
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq44 eq17 -- backward demodulation 17,44
  have eq60 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X3))) = X3 := superpose eq58 eq15 -- backward demodulation 15,58
  have eq61 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ (X0 ◇ X2)) ◇ X2) = X3 := superpose eq58 eq18 -- backward demodulation 18,58
  have eq68 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X3 := superpose eq58 eq61 -- forward demodulation 61,58
  have eq256 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X2)) := superpose eq60 eq30 -- superposition 30,60, 60 into 30, unify on (0).2 in 60 and (0).2.1 in 30
  have eq292 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := superpose eq256 eq10 -- backward demodulation 10,256
  subsumption eq292 eq68


@[equational_result]
theorem Equation2113_implies_Equation3161 (G : Type*) [Magma G] (h : Equation2113 G) : Equation3161 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK2) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = (X3 ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.2 in 12
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq40 (X1 X3 : G) : ((X3 ◇ X1) ◇ X3) = X1 := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).1 in 30
  have eq44 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).2.1 in 30
  have eq45 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ X1) = ((X2 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq11 eq30 -- superposition 30,11, 11 into 30, unify on (0).2 in 11 and (0).2.1 in 30
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq44 eq17 -- backward demodulation 17,44
  have eq87 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK1 ◇ sK0)) ◇ sK2) := superpose eq45 eq10 -- backward demodulation 10,45
  have eq98 : sK0 ≠ ((sK2 ◇ sK0) ◇ sK2) := superpose eq58 eq87 -- forward demodulation 87,58
  subsumption eq98 eq40


@[equational_result]
theorem Equation2990_implies_Equation2872 (G : Type*) [Magma G] (h : Equation2990 G) : Equation2872 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : (((X2 ◇ X2) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq26 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3) ◇ X3) = X3 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.1 in 11
  have eq33 (X2 X3 X4 : G) : (((X3 ◇ (X2 ◇ X2)) ◇ X4) ◇ X4) = X4 := superpose eq9 eq26 -- superposition 26,9, 9 into 26, unify on (0).2 in 9 and (0).1.1.1.2.2 in 26
  have eq68 : sK0 ≠ sK0 := superpose eq33 eq10 -- superposition 10,33, 33 into 10, unify on (0).2 in 33 and (0).2 in 10
  subsumption eq68 rfl


@[equational_result]
theorem Equation2990_implies_Equation2899 (G : Type*) [Magma G] (h : Equation2990 G) : Equation2899 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : (((X2 ◇ X2) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq26 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3) ◇ X3) = X3 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.1 in 11
  have eq33 (X2 X3 X4 : G) : (((X3 ◇ (X2 ◇ X2)) ◇ X4) ◇ X4) = X4 := superpose eq9 eq26 -- superposition 26,9, 9 into 26, unify on (0).2 in 9 and (0).1.1.1.2.2 in 26
  have eq68 : sK0 ≠ sK0 := superpose eq33 eq10 -- superposition 10,33, 33 into 10, unify on (0).2 in 33 and (0).2 in 10
  subsumption eq68 rfl


@[equational_result]
theorem Equation2990_implies_Equation3007 (G : Type*) [Magma G] (h : Equation2990 G) : Equation3007 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK2)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : (((X2 ◇ X2) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq26 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3) ◇ X3) = X3 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.1 in 11
  have eq33 (X2 X3 X4 : G) : (((X3 ◇ (X2 ◇ X2)) ◇ X4) ◇ X4) = X4 := superpose eq9 eq26 -- superposition 26,9, 9 into 26, unify on (0).2 in 9 and (0).1.1.1.2.2 in 26
  have eq68 : sK0 ≠ sK0 := superpose eq33 eq10 -- superposition 10,33, 33 into 10, unify on (0).2 in 33 and (0).2 in 10
  subsumption eq68 rfl


@[equational_result]
theorem Equation3913_implies_Equation3693 (G : Type*) [Magma G] (h : Equation3913 G) : Equation3693 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X4) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq16 (X5 X6 X7 : G) : (X6 ◇ X6) = ((X5 ◇ X5) ◇ X7) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X4 X5 : G) : (X5 ◇ X5) = (X4 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq31 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (sK2 ◇ sK3)) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2.1 in 10
  subsumption eq31 eq16


@[equational_result]
theorem Equation1236_implies_Equation3256 (G : Type*) [Magma G] (h : Equation1236 G) : Equation3256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq23 : sK0 ≠ sK0 := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  subsumption eq23 rfl


@[equational_result]
theorem Equation1236_implies_Equation417 (G : Type*) [Magma G] (h : Equation1236 G) : Equation417 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1236_implies_Equation1024 (G : Type*) [Magma G] (h : Equation1236 G) : Equation1024 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK2)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation1236_implies_Equation420 (G : Type*) [Magma G] (h : Equation1236 G) : Equation420 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation1236_implies_Equation3257 (G : Type*) [Magma G] (h : Equation1236 G) : Equation3257 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2 in 13
  have eq23 : sK0 ≠ sK0 := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  subsumption eq23 rfl


@[equational_result]
theorem Equation1236_implies_Equation102 (G : Type*) [Magma G] (h : Equation1236 G) : Equation102 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ ((X0 ◇ X3) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq22 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation3910_implies_Equation3693 (G : Type*) [Magma G] (h : Equation3910 G) : Equation3693 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq25 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.1 in 9
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (sK2 ◇ sK3)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1 in 10
  subsumption eq26 eq25


@[equational_result]
theorem Equation849_implies_Equation3662 (G : Type*) [Magma G] (h : Equation849 G) : Equation3662 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq53 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq53 rfl


@[equational_result]
theorem Equation849_implies_Equation3729 (G : Type*) [Magma G] (h : Equation849 G) : Equation3729 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq53 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq53 rfl


@[equational_result]
theorem Equation849_implies_Equation1861 (G : Type*) [Magma G] (h : Equation849 G) : Equation1861 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq23 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq23 eq16


@[equational_result]
theorem Equation849_implies_Equation3256 (G : Type*) [Magma G] (h : Equation849 G) : Equation3256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq23 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq23 rfl


@[equational_result]
theorem Equation849_implies_Equation1036 (G : Type*) [Magma G] (h : Equation849 G) : Equation1036 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq23 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq23 eq16


@[equational_result]
theorem Equation849_implies_Equation3928 (G : Type*) [Magma G] (h : Equation849 G) : Equation3928 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq23 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq23 rfl


@[equational_result]
theorem Equation849_implies_Equation820 (G : Type*) [Magma G] (h : Equation849 G) : Equation820 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq23 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq23 eq16


@[equational_result]
theorem Equation849_implies_Equation3315 (G : Type*) [Magma G] (h : Equation849 G) : Equation3315 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq23 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq23 rfl


@[equational_result]
theorem Equation849_implies_Equation1028 (G : Type*) [Magma G] (h : Equation849 G) : Equation1028 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq23 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq23 eq16


@[equational_result]
theorem Equation849_implies_Equation3862 (G : Type*) [Magma G] (h : Equation849 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq15 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).1.2.1 in 12
  have eq22 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq15 eq9 -- backward demodulation 9,15
  subsumption eq22 rfl


@[equational_result]
theorem Equation849_implies_Equation436 (G : Type*) [Magma G] (h : Equation849 G) : Equation436 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq23 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq23 eq16


@[equational_result]
theorem Equation849_implies_Equation1865 (G : Type*) [Magma G] (h : Equation849 G) : Equation1865 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq23 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq23 eq16


@[equational_result]
theorem Equation849_implies_Equation3870 (G : Type*) [Magma G] (h : Equation849 G) : Equation3870 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq23 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq23 rfl


@[equational_result]
theorem Equation849_implies_Equation414 (G : Type*) [Magma G] (h : Equation849 G) : Equation414 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq23 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq23 eq16


@[equational_result]
theorem Equation849_implies_Equation823 (G : Type*) [Magma G] (h : Equation849 G) : Equation823 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation849_implies_Equation3915 (G : Type*) [Magma G] (h : Equation849 G) : Equation3915 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq23 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq23 rfl


@[equational_result]
theorem Equation849_implies_Equation1249 (G : Type*) [Magma G] (h : Equation849 G) : Equation1249 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X3 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X3)) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq16 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq48 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3)) = X1 := superpose eq16 eq14 -- superposition 14,16, 16 into 14, unify on (0).2 in 16 and (0).1.2.1.1 in 14
  have eq57 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X3)) = X1 := superpose eq16 eq48 -- forward demodulation 48,16
  have eq109 : sK0 ≠ sK0 := superpose eq57 eq10 -- superposition 10,57, 57 into 10, unify on (0).2 in 57 and (0).2 in 10
  subsumption eq109 rfl


@[equational_result]
theorem Equation849_implies_Equation4341 (G : Type*) [Magma G] (h : Equation849 G) : Equation4341 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq23 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq23 eq16


@[equational_result]
theorem Equation849_implies_Equation858 (G : Type*) [Magma G] (h : Equation849 G) : Equation858 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq23 rfl


@[equational_result]
theorem Equation849_implies_Equation851 (G : Type*) [Magma G] (h : Equation849 G) : Equation851 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X3 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X3)) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq32 (X0 X3 X4 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X4)) = X3 := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2.1 in 14
  have eq78 : sK0 ≠ sK0 := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2 in 10
  subsumption eq78 rfl


@[equational_result]
theorem Equation849_implies_Equation411 (G : Type*) [Magma G] (h : Equation849 G) : Equation411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq15 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).1.2.1 in 12
  have eq22 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq15 eq9 -- backward demodulation 9,15
  subsumption eq22 eq15


@[equational_result]
theorem Equation849_implies_Equation1225 (G : Type*) [Magma G] (h : Equation849 G) : Equation1225 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X3 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X3)) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq16 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq52 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3)) = X1 := superpose eq16 eq14 -- superposition 14,16, 16 into 14, unify on (0).2 in 16 and (0).1.2.1.1 in 14
  have eq57 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X3)) = X1 := superpose eq16 eq52 -- forward demodulation 52,16
  have eq97 : sK0 ≠ sK0 := superpose eq57 eq10 -- superposition 10,57, 57 into 10, unify on (0).2 in 57 and (0).2 in 10
  subsumption eq97 rfl


@[equational_result]
theorem Equation849_implies_Equation3319 (G : Type*) [Magma G] (h : Equation849 G) : Equation3319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq23 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq23 rfl


@[equational_result]
theorem Equation849_implies_Equation8 (G : Type*) [Magma G] (h : Equation849 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq15 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).1.2.1 in 12
  have eq47 : sK0 ≠ sK0 := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).2 in 9
  subsumption eq47 rfl


@[equational_result]
theorem Equation801_implies_Equation4138 (G : Type*) [Magma G] (h : Equation801 G) : Equation4138 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ X3) = (X4 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq31 (X0 X1 X2 : G) : (sK0 ◇ sK1) ≠ ((X0 ◇ (X1 ◇ X2)) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq31 eq13


@[equational_result]
theorem Equation801_implies_Equation4320 (G : Type*) [Magma G] (h : Equation801 G) : Equation4320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X3 ◇ X2) ◇ X4)) = (X5 ◇ (X1 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ X3) = (X4 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X3 X4 X5 : G) : (X3 ◇ X4) = (X5 ◇ X4) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq44 (X2 X3 X4 X5 X6 : G) : (X3 ◇ (X4 ◇ X2)) = (X5 ◇ (X6 ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq111 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (X0 ◇ sK0)) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2.2 in 10
  subsumption eq111 eq44


@[equational_result]
theorem Equation801_implies_Equation4090 (G : Type*) [Magma G] (h : Equation801 G) : Equation4090 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ X3) = (X4 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq30 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ (X1 ◇ X2)) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq30 eq13


@[equational_result]
theorem Equation801_implies_Equation4374 (G : Type*) [Magma G] (h : Equation801 G) : Equation4374 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq12 (X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X3 ◇ X2) ◇ X4)) = (X5 ◇ (X1 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ X3) = (X4 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X3 X4 X5 : G) : (X3 ◇ X4) = (X5 ◇ X4) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq44 (X2 X3 X4 X5 X6 : G) : (X3 ◇ (X4 ◇ X2)) = (X5 ◇ (X6 ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq111 (X0 : G) : (sK0 ◇ (X0 ◇ sK2)) ≠ (sK3 ◇ (X0 ◇ sK2)) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).1.2 in 10
  subsumption eq111 eq44


@[equational_result]
theorem Equation801_implies_Equation82 (G : Type*) [Magma G] (h : Equation801 G) : Equation82 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X3 ◇ X2) ◇ X4)) = (X5 ◇ (X1 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ X3) = (X4 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X3 X4 X5 : G) : (X3 ◇ X4) = (X5 ◇ X4) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq41 (X1 X2 X3 X4 X5 X6 X7 : G) : (X6 ◇ (X7 ◇ (X2 ◇ X3))) = (X1 ◇ (X4 ◇ ((X5 ◇ X4) ◇ X3))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq76 (X2 X3 X6 X7 : G) : (X6 ◇ (X7 ◇ (X2 ◇ X3))) = X3 := superpose eq9 eq41 -- forward demodulation 41,9
  have eq111 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (X0 ◇ sK0))) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2.2.2 in 10
  subsumption eq111 eq76


@[equational_result]
theorem Equation2250_implies_Equation2287 (G : Type*) [Magma G] (h : Equation2250 G) : Equation2287 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq59 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.1 in 19
  have eq82 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq59 eq9 -- superposition 9,59, 59 into 9, unify on (0).2 in 59 and (0).1.1 in 9
  have eq99 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq82 eq19 -- backward demodulation 19,82
  have eq126 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = X0 := superpose eq99 eq9 -- backward demodulation 9,99
  have eq131 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq99 eq82 -- backward demodulation 82,99
  have eq200 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq131 eq126 -- superposition 126,131, 131 into 126, unify on (0).2 in 131 and (0).1.1 in 126
  have eq201 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq131 eq200 -- forward demodulation 200,131
  have eq219 : sK0 ≠ sK0 := superpose eq201 eq10 -- superposition 10,201, 201 into 10, unify on (0).2 in 201 and (0).2 in 10
  subsumption eq219 rfl


@[equational_result]
theorem Equation3957_implies_Equation3971 (G : Type*) [Magma G] (h : Equation3957 G) : Equation3971 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X3 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = (((X1 ◇ X2) ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.2 in 12
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X0) = ((((X0 ◇ X2) ◇ X1) ◇ X0) ◇ X1) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq20 (X0 X1 X2 X4 : G) : (X0 ◇ X4) = ((X4 ◇ (((X0 ◇ X2) ◇ X1) ◇ X0)) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.2 in 9
  have eq22 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X4) = ((X4 ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq24 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4)) ◇ X5) = ((X5 ◇ (((X0 ◇ X2) ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.1.2 in 11
  have eq36 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X2) = (X2 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X4)) ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq41 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((((X1 ◇ X0) ◇ X3) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.1.1.1 in 19
  have eq45 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.1.1 in 19
  have eq49 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq19 eq19 -- superposition 19,19, 19 into 19, unify on (0).2 in 19 and (0).2.1 in 19
  have eq51 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = (((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X1 ◇ X0)) := superpose eq11 eq19 -- superposition 19,11, 11 into 19, unify on (0).2 in 11 and (0).2.1 in 19
  have eq52 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq87 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = (X0 ◇ (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X3) ◇ X0)) := superpose eq19 eq20 -- superposition 20,19, 19 into 20, unify on (0).2 in 19 and (0).2 in 20
  have eq102 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X3) ◇ X0)) := superpose eq52 eq87 -- forward demodulation 87,52
  have eq110 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq45 eq45 -- superposition 45,45, 45 into 45, unify on (0).2 in 45 and (0).1 in 45
  have eq113 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq45 eq45 -- superposition 45,45, 45 into 45, unify on (0).2 in 45 and (0).2.1 in 45
  have eq121 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := superpose eq45 eq19 -- superposition 19,45, 45 into 19, unify on (0).2 in 45 and (0).2.1 in 19
  have eq125 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = ((X2 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq45 eq9 -- superposition 9,45, 45 into 9, unify on (0).2 in 45 and (0).2.1.2 in 9
  have eq127 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2))) := superpose eq45 eq11 -- superposition 11,45, 45 into 11, unify on (0).2 in 45 and (0).2.1.2 in 11
  have eq132 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ (X0 ◇ X3))) = ((X1 ◇ (X0 ◇ X3)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) := superpose eq45 eq11 -- superposition 11,45, 45 into 11, unify on (0).2 in 45 and (0).2.1 in 11
  have eq133 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) := superpose eq45 eq9 -- superposition 9,45, 45 into 9, unify on (0).2 in 45 and (0).2.1 in 9
  have eq134 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = (((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X3)) ◇ X0) := superpose eq45 eq12 -- superposition 12,45, 45 into 12, unify on (0).2 in 45 and (0).1.2 in 12
  have eq139 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq121 eq113 -- backward demodulation 113,121
  have eq141 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) := superpose eq121 eq110 -- backward demodulation 110,121
  have eq145 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := superpose eq121 eq125 -- forward demodulation 125,121
  have eq147 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq121 eq127 -- forward demodulation 127,121
  have eq155 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ (X0 ◇ X3))) = ((X1 ◇ (X0 ◇ X3)) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq121 eq132 -- forward demodulation 132,121
  have eq156 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq121 eq133 -- forward demodulation 133,121
  have eq157 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq156 eq12 -- backward demodulation 12,156
  have eq163 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4)) ◇ X5) = ((X5 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4))) := superpose eq156 eq24 -- backward demodulation 24,156
  have eq185 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (((X0 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) ◇ X0)) := superpose eq156 eq102 -- backward demodulation 102,156
  have eq203 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X0)))) := superpose eq15 eq185 -- forward demodulation 185,15
  have eq205 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = (((X0 ◇ X1) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0) := superpose eq121 eq134 -- forward demodulation 134,121
  have eq208 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X4))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq157 -- superposition 157,9, 9 into 157, unify on (0).2 in 9 and (0).1.2.2.1 in 157
  have eq227 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq121 -- superposition 121,9, 9 into 121, unify on (0).2 in 9 and (0).2.1 in 121
  have eq229 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq121 eq121 -- superposition 121,121, 121 into 121, unify on (0).2 in 121 and (0).2.1 in 121
  have eq241 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = ((X0 ◇ X2) ◇ X0) := superpose eq227 eq156 -- backward demodulation 156,227
  have eq242 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = ((X1 ◇ X0) ◇ X1) := superpose eq227 eq157 -- backward demodulation 157,227
  have eq243 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4)) ◇ X5) = ((X5 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4))) := superpose eq227 eq163 -- backward demodulation 163,227
  have eq252 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = ((((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq227 eq205 -- backward demodulation 205,227
  have eq253 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X0))) = ((X0 ◇ X3) ◇ X0) := superpose eq241 eq15 -- backward demodulation 15,241
  have eq255 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X3) ◇ X0)) := superpose eq253 eq203 -- backward demodulation 203,253
  have eq258 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X4)) ◇ X0)) = ((((X2 ◇ X3) ◇ X0) ◇ (X2 ◇ X3)) ◇ X2) := superpose eq253 eq36 -- backward demodulation 36,253
  have eq259 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X4)) ◇ X0)) = (X2 ◇ ((X2 ◇ X3) ◇ X0)) := superpose eq9 eq258 -- forward demodulation 258,9
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = (X0 ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq252 -- forward demodulation 252,9
  have eq267 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq229 eq49 -- backward demodulation 49,229
  have eq271 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq229 eq141 -- backward demodulation 141,229
  have eq272 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ X1)) := superpose eq229 eq227 -- backward demodulation 227,229
  have eq275 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = (X1 ◇ (X0 ◇ X1)) := superpose eq229 eq242 -- backward demodulation 242,229
  have eq276 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4)) ◇ X5) = ((X5 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4))) := superpose eq229 eq243 -- backward demodulation 243,229
  have eq281 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X0))) = (X0 ◇ (X3 ◇ X0)) := superpose eq229 eq253 -- backward demodulation 253,229
  have eq282 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X3 ◇ X0))) := superpose eq229 eq255 -- backward demodulation 255,229
  have eq304 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1)) := superpose eq121 eq275 -- superposition 275,121, 121 into 275, unify on (0).2 in 121 and (0).1.2 in 275
  have eq319 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1)) := superpose eq263 eq304 -- forward demodulation 304,263
  have eq342 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X0)) = (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq121 eq281 -- superposition 281,121, 121 into 281, unify on (0).2 in 121 and (0).1.2 in 281
  have eq354 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq281 eq121 -- superposition 121,281, 281 into 121, unify on (0).2 in 281 and (0).2.1 in 121
  have eq366 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq229 -- superposition 229,9, 9 into 229, unify on (0).2 in 9 and (0).1.1 in 229
  have eq369 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq229 eq229 -- superposition 229,229, 229 into 229, unify on (0).2 in 229 and (0).1.1 in 229
  have eq370 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X0 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X0)) := superpose eq275 eq229 -- superposition 229,275, 275 into 229, unify on (0).2 in 275 and (0).1.1 in 229
  have eq371 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq281 eq229 -- superposition 229,281, 281 into 229, unify on (0).2 in 281 and (0).1.1 in 229
  have eq372 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq229 -- superposition 229,9, 9 into 229, unify on (0).2 in 9 and (0).1 in 229
  have eq390 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq272 eq366 -- forward demodulation 366,272
  have eq391 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq145 eq369 -- forward demodulation 369,145
  have eq392 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq229 eq391 -- forward demodulation 391,229
  have eq393 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X0)) := superpose eq267 eq370 -- forward demodulation 370,267
  have eq394 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq393 eq319 -- backward demodulation 319,393
  have eq395 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X4)) ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq394 eq259 -- backward demodulation 259,394
  have eq404 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq267 eq371 -- forward demodulation 371,267
  have eq405 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq404 eq342 -- backward demodulation 342,404
  have eq407 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ X3) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq405 eq147 -- backward demodulation 147,405
  have eq409 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq229 eq372 -- forward demodulation 372,229
  have eq410 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq409 eq282 -- backward demodulation 282,409
  have eq417 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq410 eq392 -- backward demodulation 392,410
  have eq420 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X4)) ◇ X0)) = (X2 ◇ X2) := superpose eq410 eq395 -- backward demodulation 395,410
  have eq432 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X3) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq410 eq407 -- backward demodulation 407,410
  have eq436 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X0)) := superpose eq410 eq51 -- backward demodulation 51,410
  have eq469 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq420 -- superposition 420,9, 9 into 420, unify on (0).2 in 9 and (0).1.2 in 420
  have eq494 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ X1) := superpose eq469 eq272 -- backward demodulation 272,469
  have eq497 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq494 eq271 -- backward demodulation 271,494
  have eq500 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = (X1 ◇ X1) := superpose eq494 eq275 -- backward demodulation 275,494
  have eq501 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4)) ◇ X5) = ((X5 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4))) := superpose eq494 eq276 -- backward demodulation 276,494
  have eq513 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq494 eq354 -- backward demodulation 354,494
  have eq519 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X1)) := superpose eq494 eq390 -- backward demodulation 390,494
  have eq524 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq494 eq417 -- backward demodulation 417,494
  have eq534 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = ((X1 ◇ X1) ◇ X0) := superpose eq432 eq519 -- forward demodulation 519,432
  have eq536 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = (((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X0)) := superpose eq534 eq436 -- backward demodulation 436,534
  have eq546 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq410 -- superposition 410,9, 9 into 410, unify on (0).2 in 9 and (0).1.2 in 410
  have eq564 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := superpose eq546 eq536 -- backward demodulation 536,546
  have eq571 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X4))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq500 -- superposition 500,9, 9 into 500, unify on (0).2 in 9 and (0).1.2.2.1 in 500
  have eq574 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq139 eq500 -- superposition 500,139, 139 into 500, unify on (0).2 in 139 and (0).1.2.2.1 in 500
  have eq589 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq420 eq500 -- superposition 500,420, 420 into 500, unify on (0).2 in 420 and (0).1.2 in 500
  have eq591 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ X1) := superpose eq500 eq500 -- superposition 500,500, 500 into 500, unify on (0).2 in 500 and (0).1.2 in 500
  have eq604 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X4))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) := superpose eq546 eq571 -- forward demodulation 571,546
  have eq605 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq604 eq208 -- backward demodulation 208,604
  have eq609 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ (X0 ◇ X3))) = ((X1 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X1)) := superpose eq605 eq155 -- backward demodulation 155,605
  have eq610 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X3) := superpose eq609 eq41 -- backward demodulation 41,609
  have eq618 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq524 eq589 -- forward demodulation 589,524
  have eq626 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq618 eq546 -- backward demodulation 546,618
  have eq631 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq626 eq564 -- backward demodulation 564,626
  have eq641 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ X0) ◇ X3) := superpose eq626 eq610 -- backward demodulation 610,626
  have eq646 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq497 eq631 -- forward demodulation 631,497
  have eq653 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq646 eq574 -- backward demodulation 574,646
  have eq654 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = (X0 ◇ X0) := superpose eq653 eq513 -- backward demodulation 513,653
  have eq657 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq654 eq10 -- backward demodulation 10,654
  have eq659 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq646 eq641 -- forward demodulation 641,646
  have eq670 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X4) = ((X4 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq659 eq22 -- backward demodulation 22,659
  have eq679 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X4) = (X1 ◇ X4) := superpose eq9 eq670 -- forward demodulation 670,9
  have eq685 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) = ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq11 eq591 -- superposition 591,11, 11 into 591, unify on (0).2 in 11 and (0).1 in 591
  have eq703 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) = ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq591 eq11 -- superposition 11,591, 591 into 11, unify on (0).2 in 591 and (0).2 in 11
  have eq724 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) := superpose eq659 eq685 -- forward demodulation 685,659
  have eq725 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ X0) := superpose eq618 eq724 -- forward demodulation 724,618
  have eq726 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq646 eq725 -- forward demodulation 725,646
  have eq731 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) := superpose eq726 eq703 -- forward demodulation 703,726
  have eq732 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq646 eq731 -- forward demodulation 731,646
  have eq733 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := superpose eq659 eq732 -- forward demodulation 732,659
  have eq737 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4)) ◇ X5) = ((X5 ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4))) := superpose eq733 eq501 -- backward demodulation 501,733
  have eq778 (X0 X1 X3 X4 : G) : (X1 ◇ X4) = ((X1 ◇ ((X0 ◇ X1) ◇ X3)) ◇ X4) := superpose eq733 eq679 -- backward demodulation 679,733
  have eq797 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4)) ◇ X5) = ((X5 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) := superpose eq733 eq737 -- forward demodulation 737,733
  have eq798 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4)) ◇ X5) = ((X5 ◇ X0) ◇ X1) := superpose eq733 eq797 -- forward demodulation 797,733
  have eq799 (X0 X1 X2 X3 X5 : G) : ((X5 ◇ X0) ◇ X1) = (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X0) ◇ X5) := superpose eq733 eq798 -- forward demodulation 798,733
  have eq800 (X0 X1 X2 X5 : G) : ((X5 ◇ X0) ◇ X1) = (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X5) := superpose eq733 eq799 -- forward demodulation 799,733
  have eq801 (X0 X1 X5 : G) : ((X5 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X5) := superpose eq733 eq800 -- forward demodulation 800,733
  have eq802 (X0 X1 X5 : G) : ((X0 ◇ X1) ◇ X5) = ((X5 ◇ X0) ◇ X1) := superpose eq121 eq801 -- forward demodulation 801,121
  have eq838 (X0 X1 X4 : G) : (X1 ◇ X4) = ((X1 ◇ (X0 ◇ X1)) ◇ X4) := superpose eq733 eq778 -- forward demodulation 778,733
  have eq839 (X1 X4 : G) : (X1 ◇ X4) = ((X1 ◇ X1) ◇ X4) := superpose eq494 eq838 -- forward demodulation 838,494
  have eq853 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq591 eq839 -- superposition 839,591, 591 into 839, unify on (0).2 in 591 and (0).2.1 in 839
  have eq866 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq733 eq853 -- forward demodulation 853,733
  have eq874 (X0 X1 X5 : G) : (X0 ◇ X5) = ((X5 ◇ X0) ◇ X1) := superpose eq866 eq802 -- backward demodulation 802,866
  have eq901 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq839 eq874 -- superposition 874,839, 839 into 874, unify on (0).2 in 839 and (0).2 in 874
  have eq932 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq901 eq657 -- superposition 657,901, 901 into 657, unify on (0).2 in 901 and (0).1 in 657
  subsumption eq932 rfl


@[equational_result]
theorem Equation3498_implies_Equation4351 (G : Type*) [Magma G] (h : Equation3498 G) : Equation4351 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X1) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq15 (X1 X4 X5 : G) : (X5 ◇ X5) = (X1 ◇ (X4 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq58 eq15


@[equational_result]
theorem Equation3498_implies_Equation3286 (G : Type*) [Magma G] (h : Equation3498 G) : Equation3286 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X1) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq15 (X1 X4 X5 : G) : (X5 ◇ X5) = (X1 ◇ (X4 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq58 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq58 eq15


@[equational_result]
theorem Equation3498_implies_Equation3668 (G : Type*) [Magma G] (h : Equation3498 G) : Equation3668 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X1) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq15 (X1 X4 X5 : G) : (X5 ◇ X5) = (X1 ◇ (X4 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2 in 10
  subsumption eq26 eq15


@[equational_result]
theorem Equation3498_implies_Equation3465 (G : Type*) [Magma G] (h : Equation3498 G) : Equation3465 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X1) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2.1 in 9
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ ((X0 ◇ X0) ◇ sK1)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2.1 in 10
  subsumption eq26 eq24


@[equational_result]
theorem Equation3498_implies_Equation3502 (G : Type*) [Magma G] (h : Equation3498 G) : Equation3502 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X1) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2.1 in 9
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ ((X0 ◇ X0) ◇ sK3)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2.1 in 10
  subsumption eq26 eq24


@[equational_result]
theorem Equation3498_implies_Equation3256 (G : Type*) [Magma G] (h : Equation3498 G) : Equation3256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X1) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq15 (X1 X4 X5 : G) : (X5 ◇ X5) = (X1 ◇ (X4 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq58 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq58 eq15


@[equational_result]
theorem Equation3498_implies_Equation3272 (G : Type*) [Magma G] (h : Equation3498 G) : Equation3272 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X1) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq15 (X1 X4 X5 : G) : (X5 ◇ X5) = (X1 ◇ (X4 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq58 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq58 eq15


@[equational_result]
theorem Equation3498_implies_Equation3262 (G : Type*) [Magma G] (h : Equation3498 G) : Equation3262 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X1) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq15 (X1 X4 X5 : G) : (X5 ◇ X5) = (X1 ◇ (X4 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq58 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq58 eq15


@[equational_result]
theorem Equation3498_implies_Equation3466 (G : Type*) [Magma G] (h : Equation3498 G) : Equation3466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X1) ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2.1 in 9
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ ((X0 ◇ X0) ◇ sK2)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2.1 in 10
  subsumption eq26 eq24


@[equational_result]
theorem Equation3089_implies_Equation3052 (G : Type*) [Magma G] (h : Equation3089 G) : Equation3052 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (((X0 ◇ X3) ◇ X0) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1.1 in 9
  have eq42 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X3) ◇ X4) ◇ X3) = ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) ◇ ((((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X3) ◇ X4) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq45 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X4) ◇ X5) ◇ X4) = (((((X0 ◇ X2) ◇ X3) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X4) ◇ X5) ◇ X4)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1.1 in 11
  have eq450 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X4) ◇ X3) = ((X0 ◇ (((X0 ◇ X1) ◇ ((((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X4) ◇ X3)) ◇ X1)) ◇ ((((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X4) ◇ X3)) := superpose eq45 eq42 -- superposition 42,45, 45 into 42, unify on (0).2 in 45 and (0).1 in 42
  have eq451 (X0 X1 X2 X3 X4 X5 : G) : (((((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ X4) ◇ X3) ◇ X5) ◇ (((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ X4) ◇ X3)) = (((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X0)) ◇ X1) ◇ ((X0 ◇ X2) ◇ X0))) ◇ (((((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ X4) ◇ X3) ◇ X5) ◇ (((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ X4) ◇ X3))) := superpose eq45 eq42 -- superposition 42,45, 45 into 42, unify on (0).2 in 45 and (0).1.1.1 in 42
  have eq7698 (X0 X1 X2 X3 X4 : G) : ((((((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) ◇ X2) ◇ X4) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) ◇ X2)) ◇ X0) = X0 := superpose eq451 eq9 -- superposition 9,451, 451 into 9, unify on (0).2 in 451 and (0).1.1 in 9
  have eq8527 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) ◇ X2)) := superpose eq7698 eq9 -- superposition 9,7698, 7698 into 9, unify on (0).2 in 7698 and (0).1.1 in 9
  have eq8531 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X4) ◇ X3) = ((X0 ◇ (((((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X4) ◇ X3) ◇ X1)) ◇ ((((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X4) ◇ X3)) := superpose eq8527 eq450 -- backward demodulation 450,8527
  have eq9330 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X0) = ((X0 ◇ (((X0 ◇ X3) ◇ X0) ◇ X1)) ◇ ((X0 ◇ X3) ◇ X0)) := superpose eq16 eq8531 -- superposition 8531,16, 16 into 8531, unify on (0).2 in 16 and (0).1.1.1 in 8531
  have eq9554 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X0) = X0 := superpose eq9330 eq9 -- superposition 9,9330, 9330 into 9, unify on (0).2 in 9330 and (0).1.1.1 in 9
  have eq9565 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq12 eq9554 -- forward demodulation 9554,12
  have eq10316 : sK0 ≠ sK0 := superpose eq9565 eq10 -- superposition 10,9565, 9565 into 10, unify on (0).2 in 9565 and (0).2 in 10
  subsumption eq10316 rfl


@[equational_result]
theorem Equation3089_implies_Equation3071 (G : Type*) [Magma G] (h : Equation3089 G) : Equation3071 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (((X0 ◇ X3) ◇ X0) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1.1 in 9
  have eq42 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X3) ◇ X4) ◇ X3) = ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) ◇ ((((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X3) ◇ X4) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq45 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X4) ◇ X5) ◇ X4) = (((((X0 ◇ X2) ◇ X3) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X4) ◇ X5) ◇ X4)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1.1 in 11
  have eq437 (X0 X1 X2 X3 X4 X5 : G) : (((((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ X4) ◇ X3) ◇ X5) ◇ (((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ X4) ◇ X3)) = (((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X0)) ◇ X1) ◇ ((X0 ◇ X2) ◇ X0))) ◇ (((((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ X4) ◇ X3) ◇ X5) ◇ (((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ X4) ◇ X3))) := superpose eq45 eq42 -- superposition 42,45, 45 into 42, unify on (0).2 in 45 and (0).1.1.1 in 42
  have eq439 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X4) ◇ X3) = ((X0 ◇ (((X0 ◇ X1) ◇ ((((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X4) ◇ X3)) ◇ X1)) ◇ ((((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X4) ◇ X3)) := superpose eq45 eq42 -- superposition 42,45, 45 into 42, unify on (0).2 in 45 and (0).1 in 42
  have eq7712 (X0 X1 X2 X3 X4 : G) : ((((((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) ◇ X2) ◇ X4) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) ◇ X2)) ◇ X0) = X0 := superpose eq437 eq9 -- superposition 9,437, 437 into 9, unify on (0).2 in 437 and (0).1.1 in 9
  have eq8457 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) ◇ X2)) := superpose eq7712 eq9 -- superposition 9,7712, 7712 into 9, unify on (0).2 in 7712 and (0).1.1 in 9
  have eq8461 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X4) ◇ X3) = ((X0 ◇ (((((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X4) ◇ X3) ◇ X1)) ◇ ((((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X4) ◇ X3)) := superpose eq8457 eq439 -- backward demodulation 439,8457
  have eq8678 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X0) = ((X0 ◇ (((X0 ◇ X3) ◇ X0) ◇ X1)) ◇ ((X0 ◇ X3) ◇ X0)) := superpose eq17 eq8461 -- superposition 8461,17, 17 into 8461, unify on (0).2 in 17 and (0).1.1.1 in 8461
  have eq9013 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X0) = X0 := superpose eq8678 eq9 -- superposition 9,8678, 8678 into 9, unify on (0).2 in 8678 and (0).1.1.1 in 9
  have eq9024 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq12 eq9013 -- forward demodulation 9013,12
  have eq9612 : sK0 ≠ sK0 := superpose eq9024 eq10 -- superposition 10,9024, 9024 into 10, unify on (0).2 in 9024 and (0).2 in 10
  subsumption eq9612 rfl


@[equational_result]
theorem Equation3089_implies_Equation3065 (G : Type*) [Magma G] (h : Equation3089 G) : Equation3065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (((X0 ◇ X3) ◇ X0) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1.1 in 9
  have eq42 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X3) ◇ X4) ◇ X3) = ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) ◇ ((((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X3) ◇ X4) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq45 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X4) ◇ X5) ◇ X4) = (((((X0 ◇ X2) ◇ X3) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X4) ◇ X5) ◇ X4)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1.1 in 11
  have eq437 (X0 X1 X2 X3 X4 X5 : G) : (((((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ X4) ◇ X3) ◇ X5) ◇ (((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ X4) ◇ X3)) = (((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X0)) ◇ X1) ◇ ((X0 ◇ X2) ◇ X0))) ◇ (((((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ X4) ◇ X3) ◇ X5) ◇ (((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ X4) ◇ X3))) := superpose eq45 eq42 -- superposition 42,45, 45 into 42, unify on (0).2 in 45 and (0).1.1.1 in 42
  have eq439 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X4) ◇ X3) = ((X0 ◇ (((X0 ◇ X1) ◇ ((((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X4) ◇ X3)) ◇ X1)) ◇ ((((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X4) ◇ X3)) := superpose eq45 eq42 -- superposition 42,45, 45 into 42, unify on (0).2 in 45 and (0).1 in 42
  have eq7740 (X0 X1 X2 X3 X4 : G) : ((((((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) ◇ X2) ◇ X4) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) ◇ X2)) ◇ X0) = X0 := superpose eq437 eq9 -- superposition 9,437, 437 into 9, unify on (0).2 in 437 and (0).1.1 in 9
  have eq7837 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) ◇ X2)) := superpose eq7740 eq9 -- superposition 9,7740, 7740 into 9, unify on (0).2 in 7740 and (0).1.1 in 9
  have eq7841 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X4) ◇ X3) = ((X0 ◇ (((((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X4) ◇ X3) ◇ X1)) ◇ ((((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X4) ◇ X3)) := superpose eq7837 eq439 -- backward demodulation 439,7837
  have eq8790 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X0) = ((X0 ◇ (((X0 ◇ X3) ◇ X0) ◇ X1)) ◇ ((X0 ◇ X3) ◇ X0)) := superpose eq17 eq7841 -- superposition 7841,17, 17 into 7841, unify on (0).2 in 17 and (0).1.1.1 in 7841
  have eq8816 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X0) = X0 := superpose eq8790 eq9 -- superposition 9,8790, 8790 into 9, unify on (0).2 in 8790 and (0).1.1.1 in 9
  have eq8827 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq12 eq8816 -- forward demodulation 8816,12
  have eq8928 : sK0 ≠ sK0 := superpose eq8827 eq10 -- superposition 10,8827, 8827 into 10, unify on (0).2 in 8827 and (0).2 in 10
  subsumption eq8928 rfl


@[equational_result]
theorem Equation1237_implies_Equation824 (G : Type*) [Magma G] (h : Equation1237 G) : Equation824 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ ((X0 ◇ X4) ◇ X5)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1237_implies_Equation1033 (G : Type*) [Magma G] (h : Equation1237 G) : Equation1033 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ ((X0 ◇ X4) ◇ X5)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation1237_implies_Equation1034 (G : Type*) [Magma G] (h : Equation1237 G) : Equation1034 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK3)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ ((X0 ◇ X4) ◇ X5)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation1237_implies_Equation1024 (G : Type*) [Magma G] (h : Equation1237 G) : Equation1024 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ ((X0 ◇ X4) ◇ X5)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


