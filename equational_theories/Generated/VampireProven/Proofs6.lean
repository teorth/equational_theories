import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation62_implies_Equation719 (G : Type*) [Magma G] (h : Equation62 G) : Equation719 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq17 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X1 ◇ X0) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq31 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).2.2 in 11
  have eq38 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq31 eq10 -- backward demodulation 10,31
  subsumption eq38 eq9


@[equational_result]
theorem Equation686_implies_Equation4158 (G : Type*) [Magma G] (h : Equation686 G) : Equation4158 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X1)) = (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X1)) = (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 (X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) = (X3 ◇ (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq22 (X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) = (X3 ◇ X1) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq23 (X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1) = (X3 ◇ X1) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq45 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq23 eq23 -- superposition 23,23, 23 into 23, unify on (0).2 in 23 and (0).1 in 23
  have eq82 (X0 : G) : (sK0 ◇ sK1) ≠ (((X0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq45 eq10 -- superposition 10,45, 45 into 10, unify on (0).2 in 45 and (0).2.1.1 in 10
  subsumption eq82 eq45


@[equational_result]
theorem Equation686_implies_Equation4693 (G : Type*) [Magma G] (h : Equation686 G) : Equation4693 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK3 ◇ sK4) ◇ sK2) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X1)) = (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X1)) = (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 (X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) = (X3 ◇ (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq22 (X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) = (X3 ◇ X1) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq23 (X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1) = (X3 ◇ X1) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq45 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq23 eq23 -- superposition 23,23, 23 into 23, unify on (0).2 in 23 and (0).1 in 23
  have eq82 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ ((X0 ◇ sK4) ◇ sK2) := superpose eq45 eq10 -- superposition 10,45, 45 into 10, unify on (0).2 in 45 and (0).2.1 in 10
  subsumption eq82 eq45


@[equational_result]
theorem Equation686_implies_Equation62 (G : Type*) [Magma G] (h : Equation686 G) : Equation62 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X1)) = (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X1)) = (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 (X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) = (X3 ◇ (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq22 (X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) = (X3 ◇ X1) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq23 (X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1) = (X3 ◇ X1) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq45 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq23 eq23 -- superposition 23,23, 23 into 23, unify on (0).2 in 23 and (0).1 in 23
  have eq93 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X1))) = X1 := superpose eq45 eq9 -- superposition 9,45, 45 into 9, unify on (0).2 in 45 and (0).1.2.2 in 9
  have eq96 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ (X0 ◇ sK0))) := superpose eq45 eq10 -- superposition 10,45, 45 into 10, unify on (0).2 in 45 and (0).2.2.2 in 10
  subsumption eq96 eq93


@[equational_result]
theorem Equation1498_implies_Equation686 (G : Type*) [Magma G] (h : Equation1498 G) : Equation686 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK2 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = (X1 ◇ (X3 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X1 ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq26 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq27 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.2 in 11
  have eq36 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq26 -- forward demodulation 26,9
  have eq37 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq27 -- forward demodulation 27,9
  have eq40 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq36 eq11 -- superposition 11,36, 36 into 11, unify on (0).2 in 36 and (0).2.2.2 in 11
  have eq47 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq40 eq10 -- backward demodulation 10,40
  have eq51 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := superpose eq37 eq37 -- superposition 37,37, 37 into 37, unify on (0).2 in 37 and (0).1 in 37
  have eq63 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq37 eq9 -- superposition 9,37, 37 into 9, unify on (0).2 in 37 and (0).1.2 in 9
  have eq98 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ (X0 ◇ sK0))) := superpose eq40 eq47 -- superposition 47,40, 40 into 47, unify on (0).2 in 40 and (0).2.2 in 47
  have eq181 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X3 ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq51 eq51 -- superposition 51,51, 51 into 51, unify on (0).2 in 51 and (0).1.2 in 51
  have eq255 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X3 ◇ (X1 ◇ X0))) = X0 := superpose eq63 eq181 -- forward demodulation 181,63
  have eq294 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq37 eq32 -- superposition 32,37, 37 into 32, unify on (0).2 in 37 and (0).2.2 in 32
  have eq321 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq255 eq294 -- forward demodulation 294,255
  have eq322 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq321 -- forward demodulation 321,9
  have eq354 : sK0 ≠ sK0 := superpose eq322 eq98 -- superposition 98,322, 322 into 98, unify on (0).2 in 322 and (0).2 in 98
  subsumption eq354 rfl


@[equational_result]
theorem Equation1498_implies_Equation639 (G : Type*) [Magma G] (h : Equation1498 G) : Equation639 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = (X1 ◇ (X3 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X1 ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq26 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq27 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).2.2.2 in 11
  have eq32 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.2 in 11
  have eq36 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq26 -- forward demodulation 26,9
  have eq37 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq27 -- forward demodulation 27,9
  have eq40 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq36 eq11 -- superposition 11,36, 36 into 11, unify on (0).2 in 36 and (0).2.2.2 in 11
  have eq50 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := superpose eq40 eq40 -- superposition 40,40, 40 into 40, unify on (0).2 in 40 and (0).1 in 40
  have eq54 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq40 eq12 -- superposition 12,40, 40 into 12, unify on (0).2 in 40 and (0).2.1 in 12
  have eq55 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq40 eq9 -- superposition 9,40, 40 into 9, unify on (0).2 in 40 and (0).1.2 in 9
  have eq56 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq40 eq11 -- superposition 11,40, 40 into 11, unify on (0).2 in 40 and (0).2.2 in 11
  have eq107 (X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ X1) = ((X2 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X2 ◇ (X1 ◇ X1)))) := superpose eq9 eq50 -- superposition 50,9, 9 into 50, unify on (0).2 in 9 and (0).1.2 in 50
  have eq113 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X3 ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq50 eq50 -- superposition 50,50, 50 into 50, unify on (0).2 in 50 and (0).1.2 in 50
  have eq161 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X2 ◇ (X1 ◇ X1)))) := superpose eq12 eq107 -- forward demodulation 107,12
  have eq162 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := superpose eq161 eq56 -- backward demodulation 56,161
  have eq166 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X3 ◇ (X1 ◇ X0))) = X0 := superpose eq55 eq113 -- forward demodulation 113,55
  have eq214 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X1 ◇ X0)) := superpose eq50 eq54 -- superposition 54,50, 50 into 54, unify on (0).2 in 50 and (0).2.1.2 in 54
  have eq240 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq55 eq214 -- forward demodulation 214,55
  have eq241 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq240 eq32 -- backward demodulation 32,240
  have eq245 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq166 eq241 -- forward demodulation 241,166
  have eq246 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq245 -- forward demodulation 245,9
  have eq376 (X0 X1 X2 : G) : (X0 ◇ X0) = (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq37 eq246 -- superposition 246,37, 37 into 246, unify on (0).2 in 37 and (0).1.2.2 in 246
  have eq412 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X0) := superpose eq55 eq376 -- forward demodulation 376,55
  have eq413 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq412 eq10 -- backward demodulation 10,412
  have eq414 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq162 eq413 -- forward demodulation 413,162
  subsumption eq414 eq246


@[equational_result]
theorem Equation901_implies_Equation1556 (G : Type*) [Magma G] (h : Equation901 G) : Equation1556 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : (X4 ◇ (X1 ◇ (X5 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X4 : G) : (X0 ◇ X1) = (X4 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 (X0 : G) : sK0 ≠ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq23 eq11


@[equational_result]
theorem Equation901_implies_Equation3955 (G : Type*) [Magma G] (h : Equation901 G) : Equation3955 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X4 : G) : (X0 ◇ X1) = (X4 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq23 eq13


@[equational_result]
theorem Equation999_implies_Equation901 (G : Type*) [Magma G] (h : Equation999 G) : Equation901 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK2) ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : (X4 ◇ (X3 ◇ (X4 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq54 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).1 in 17
  have eq73 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK3 ◇ sK0))) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2.2 in 10
  subsumption eq73 eq54


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


@[equational_result]
theorem Equation943_implies_Equation999 (G : Type*) [Magma G] (h : Equation943 G) : Equation999 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq13 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq17 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := superpose eq13 eq16 -- forward demodulation 16,13
  subsumption eq17 eq9


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
theorem Equation943_implies_Equation1531 (G : Type*) [Magma G] (h : Equation943 G) : Equation1531 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq13 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq27 (X0 : G) : sK0 ≠ ((X0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq13 eq16 -- superposition 16,13, 13 into 16, unify on (0).2 in 13 and (0).2.1 in 16
  subsumption eq27 eq23


@[equational_result]
theorem Equation811_implies_Equation912 (G : Type*) [Magma G] (h : Equation811 G) : Equation912 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X4 X5 X6 X7 : G) : (X5 ◇ (X6 ◇ (X4 ◇ X7))) = X7 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation869_implies_Equation3931 (G : Type*) [Magma G] (h : Equation869 G) : Equation3931 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq20 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 eq14


@[equational_result]
theorem Equation869_implies_Equation3952 (G : Type*) [Magma G] (h : Equation869 G) : Equation3952 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq19 (X0 : G) : (sK0 ◇ sK1) ≠ ((sK1 ◇ (X0 ◇ sK0)) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1.2 in 10
  subsumption eq19 eq14


@[equational_result]
theorem Equation869_implies_Equation716 (G : Type*) [Magma G] (h : Equation869 G) : Equation716 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq19 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq38 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK0 ◇ sK0))) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.2 in 13
  subsumption eq38 eq19


@[equational_result]
theorem Equation869_implies_Equation3905 (G : Type*) [Magma G] (h : Equation869 G) : Equation3905 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq21 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation869_implies_Equation3947 (G : Type*) [Magma G] (h : Equation869 G) : Equation3947 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK3)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq20 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 eq14


@[equational_result]
theorem Equation869_implies_Equation4083 (G : Type*) [Magma G] (h : Equation869 G) : Equation4083 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation869_implies_Equation4296 (G : Type*) [Magma G] (h : Equation869 G) : Equation4296 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq19 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq38 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2 in 13
  have eq69 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ X1)) := superpose eq19 eq19 -- superposition 19,19, 19 into 19, unify on (0).2 in 19 and (0).1.2.2 in 19
  have eq175 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq15 eq38 -- superposition 38,15, 15 into 38, unify on (0).2 in 15 and (0).1.2 in 38
  subsumption eq175 eq69


@[equational_result]
theorem Equation869_implies_Equation4086 (G : Type*) [Magma G] (h : Equation869 G) : Equation4086 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK0) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK2) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation869_implies_Equation3870 (G : Type*) [Magma G] (h : Equation869 G) : Equation3870 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq21 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation869_implies_Equation3915 (G : Type*) [Magma G] (h : Equation869 G) : Equation3915 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq16 (X0 : G) : (sK0 ◇ sK1) ≠ ((sK0 ◇ (X0 ◇ sK0)) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1.2 in 10
  subsumption eq16 eq14


@[equational_result]
theorem Equation869_implies_Equation3880 (G : Type*) [Magma G] (h : Equation869 G) : Equation3880 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation869_implies_Equation811 (G : Type*) [Magma G] (h : Equation869 G) : Equation811 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK3 ◇ sK4) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq19 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq38 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2 in 13
  subsumption eq38 eq19


@[equational_result]
theorem Equation682_implies_Equation4006 (G : Type*) [Magma G] (h : Equation682 G) : Equation4006 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq65 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq65 eq15


@[equational_result]
theorem Equation682_implies_Equation75 (G : Type*) [Magma G] (h : Equation682 G) : Equation75 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X1) ◇ X3) ◇ X2)) = (X0 ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X3) ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq52 (X0 : G) : sK0 ≠ (sK1 ◇ (sK1 ◇ (X0 ◇ sK0))) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2.2 in 10
  have eq125 (X0 X1 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ (((sK1 ◇ X0) ◇ X1) ◇ sK0))) := superpose eq12 eq52 -- superposition 52,12, 12 into 52, unify on (0).2 in 12 and (0).2.2 in 52
  subsumption eq125 eq11


@[equational_result]
theorem Equation682_implies_Equation778 (G : Type*) [Magma G] (h : Equation682 G) : Equation778 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK2 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq60 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.2 in 11
  have eq65 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (X0 ◇ sK0))) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2.2 in 10
  subsumption eq65 eq60


@[equational_result]
theorem Equation682_implies_Equation3909 (G : Type*) [Magma G] (h : Equation682 G) : Equation3909 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq65 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq65 eq15


@[equational_result]
theorem Equation682_implies_Equation4076 (G : Type*) [Magma G] (h : Equation682 G) : Equation4076 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq52 (X0 : G) : (sK0 ◇ sK0) ≠ (((X0 ◇ sK1) ◇ sK2) ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1.1 in 10
  subsumption eq52 eq15


@[equational_result]
theorem Equation682_implies_Equation4291 (G : Type*) [Magma G] (h : Equation682 G) : Equation4291 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq65 (X0 : G) : (sK0 ◇ (X0 ◇ sK1)) ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).1.2 in 10
  subsumption eq65 eq15


@[equational_result]
theorem Equation682_implies_Equation370 (G : Type*) [Magma G] (h : Equation682 G) : Equation370 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK1 ◇ sK2) ◇ sK0) ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq52 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ sK2) ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).1.1 in 10
  subsumption eq52 eq15


@[equational_result]
theorem Equation682_implies_Equation4108 (G : Type*) [Magma G] (h : Equation682 G) : Equation4108 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq65 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq65 eq15


@[equational_result]
theorem Equation682_implies_Equation4642 (G : Type*) [Magma G] (h : Equation682 G) : Equation4642 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK2 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq65 (X0 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ ((X0 ◇ sK0) ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq65 eq15


@[equational_result]
theorem Equation682_implies_Equation4112 (G : Type*) [Magma G] (h : Equation682 G) : Equation4112 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK3) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq52 (X0 : G) : (sK0 ◇ sK0) ≠ (((X0 ◇ sK2) ◇ sK3) ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1.1 in 10
  subsumption eq52 eq15


@[equational_result]
theorem Equation682_implies_Equation4150 (G : Type*) [Magma G] (h : Equation682 G) : Equation4150 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK3) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq52 (X0 : G) : (sK0 ◇ sK1) ≠ (((X0 ◇ sK2) ◇ sK3) ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1.1 in 10
  subsumption eq52 eq15


@[equational_result]
theorem Equation682_implies_Equation4675 (G : Type*) [Magma G] (h : Equation682 G) : Equation4675 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq52 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ ((X0 ◇ sK3) ◇ sK2) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq52 eq15


@[equational_result]
theorem Equation682_implies_Equation4284 (G : Type*) [Magma G] (h : Equation682 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq60 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.2 in 11
  have eq65 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  have eq123 (X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ X3)) = (X4 ◇ (X5 ◇ X3)) := superpose eq60 eq60 -- superposition 60,60, 60 into 60, unify on (0).2 in 60 and (0).1.2.2 in 60
  have eq229 (X0 X1 : G) : (sK0 ◇ (X0 ◇ sK1)) ≠ (X1 ◇ (sK1 ◇ sK1)) := superpose eq15 eq65 -- superposition 65,15, 15 into 65, unify on (0).2 in 15 and (0).1.2 in 65
  subsumption eq229 eq123


@[equational_result]
theorem Equation682_implies_Equation3893 (G : Type*) [Magma G] (h : Equation682 G) : Equation3893 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq52 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ (X0 ◇ sK2)) ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1.2 in 10
  subsumption eq52 eq15


@[equational_result]
theorem Equation682_implies_Equation1488 (G : Type*) [Magma G] (h : Equation682 G) : Equation1488 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq66 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.2 in 11
  have eq68 (X0 : G) : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ (X0 ◇ sK0))) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2.2 in 10
  subsumption eq68 eq66


@[equational_result]
theorem Equation682_implies_Equation4378 (G : Type*) [Magma G] (h : Equation682 G) : Equation4378 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK4 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq60 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.2 in 11
  have eq65 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK4 ◇ sK2)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  have eq123 (X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ X3)) = (X4 ◇ (X5 ◇ X3)) := superpose eq60 eq60 -- superposition 60,60, 60 into 60, unify on (0).2 in 60 and (0).1.2.2 in 60
  have eq229 (X0 X1 : G) : (X1 ◇ (sK4 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq15 eq65 -- superposition 65,15, 15 into 65, unify on (0).2 in 15 and (0).1.2 in 65
  subsumption eq229 eq123


@[equational_result]
theorem Equation682_implies_Equation395 (G : Type*) [Magma G] (h : Equation682 G) : Equation395 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq52 (X0 : G) : (sK0 ◇ sK1) ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq52 eq15


@[equational_result]
theorem Equation682_implies_Equation3883 (G : Type*) [Magma G] (h : Equation682 G) : Equation3883 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq65 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq65 eq15


@[equational_result]
theorem Equation682_implies_Equation4351 (G : Type*) [Magma G] (h : Equation682 G) : Equation4351 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq65 (X0 : G) : (sK0 ◇ (X0 ◇ sK1)) ≠ (sK2 ◇ (X0 ◇ sK1)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).1.2 in 10
  subsumption eq65 eq15


@[equational_result]
theorem Equation682_implies_Equation690 (G : Type*) [Magma G] (h : Equation682 G) : Equation690 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK2 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation682_implies_Equation1586 (G : Type*) [Magma G] (h : Equation682 G) : Equation1586 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq60 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.2 in 11
  have eq65 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq65 eq60


@[equational_result]
theorem Equation682_implies_Equation4040 (G : Type*) [Magma G] (h : Equation682 G) : Equation4040 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq65 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq65 eq15


@[equational_result]
theorem Equation682_implies_Equation381 (G : Type*) [Magma G] (h : Equation682 G) : Equation381 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq52 (X0 : G) : (sK0 ◇ sK1) ≠ ((X0 ◇ sK2) ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq52 eq15


@[equational_result]
theorem Equation682_implies_Equation4631 (G : Type*) [Magma G] (h : Equation682 G) : Equation4631 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq52 (X0 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ ((X0 ◇ sK2) ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq52 eq15


@[equational_result]
theorem Equation682_implies_Equation1525 (G : Type*) [Magma G] (h : Equation682 G) : Equation1525 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq60 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.2 in 11
  have eq65 (X0 : G) : sK0 ≠ (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq65 eq60


@[equational_result]
theorem Equation682_implies_Equation4001 (G : Type*) [Magma G] (h : Equation682 G) : Equation4001 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK0 ◇ sK3)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq65 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq65 eq15


@[equational_result]
theorem Equation682_implies_Equation3873 (G : Type*) [Magma G] (h : Equation682 G) : Equation3873 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq65 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq65 eq15


@[equational_result]
theorem Equation682_implies_Equation4611 (G : Type*) [Magma G] (h : Equation682 G) : Equation4611 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq52 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((X0 ◇ sK2) ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq52 eq15


@[equational_result]
theorem Equation682_implies_Equation765 (G : Type*) [Magma G] (h : Equation682 G) : Equation765 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq60 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.2 in 11
  have eq65 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (X0 ◇ sK0))) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2.2 in 10
  subsumption eq65 eq60


@[equational_result]
theorem Equation682_implies_Equation4599 (G : Type*) [Magma G] (h : Equation682 G) : Equation4599 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq65 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((X0 ◇ sK1) ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq65 eq15


@[equational_result]
theorem Equation682_implies_Equation3928 (G : Type*) [Magma G] (h : Equation682 G) : Equation3928 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq65 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq65 eq15


@[equational_result]
theorem Equation682_implies_Equation856 (G : Type*) [Magma G] (h : Equation682 G) : Equation856 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq60 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.2 in 11
  have eq65 (X0 : G) : sK0 ≠ (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq65 eq60


@[equational_result]
theorem Equation682_implies_Equation864 (G : Type*) [Magma G] (h : Equation682 G) : Equation864 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq60 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.2 in 11
  have eq65 (X0 : G) : sK0 ≠ (sK0 ◇ (X0 ◇ (sK3 ◇ sK0))) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq65 eq60


@[equational_result]
theorem Equation682_implies_Equation4677 (G : Type*) [Magma G] (h : Equation682 G) : Equation4677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK1 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq52 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ ((X0 ◇ sK0) ◇ sK2) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq52 eq15


@[equational_result]
theorem Equation682_implies_Equation916 (G : Type*) [Magma G] (h : Equation682 G) : Equation916 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq60 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.2 in 11
  have eq65 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK0 ◇ sK0))) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq65 eq60


@[equational_result]
theorem Equation682_implies_Equation1484 (G : Type*) [Magma G] (h : Equation682 G) : Equation1484 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation682_implies_Equation869 (G : Type*) [Magma G] (h : Equation682 G) : Equation869 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq60 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.2 in 11
  have eq65 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK0 ◇ sK0))) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq65 eq60


@[equational_result]
theorem Equation682_implies_Equation39 (G : Type*) [Magma G] (h : Equation682 G) : Equation39 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq52 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq52 eq15


@[equational_result]
theorem Equation985_implies_Equation3943 (G : Type*) [Magma G] (h : Equation985 G) : Equation3943 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq23 eq13


@[equational_result]
theorem Equation985_implies_Equation4209 (G : Type*) [Magma G] (h : Equation985 G) : Equation4209 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ (((X0 ◇ sK1) ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation985_implies_Equation782 (G : Type*) [Magma G] (h : Equation985 G) : Equation782 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X0 ◇ X1))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq25 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq25 eq24


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
theorem Equation985_implies_Equation625 (G : Type*) [Magma G] (h : Equation985 G) : Equation625 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X0 ◇ X1))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq25 (X0 : G) : sK0 ≠ (sK0 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  subsumption eq25 eq24


@[equational_result]
theorem Equation744_implies_Equation1518 (G : Type*) [Magma G] (h : Equation744 G) : Equation1518 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq20 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X2 ◇ X0))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq70 (X0 : G) : sK0 ≠ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq70 eq20


@[equational_result]
theorem Equation744_implies_Equation3939 (G : Type*) [Magma G] (h : Equation744 G) : Equation3939 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 (X0 : G) : (sK0 ◇ sK1) ≠ ((sK1 ◇ X0) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 eq12


@[equational_result]
theorem Equation744_implies_Equation960 (G : Type*) [Magma G] (h : Equation744 G) : Equation960 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq23 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X2 ◇ X0))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq70 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK0 ◇ sK0))) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq70 eq23


@[equational_result]
theorem Equation744_implies_Equation1594 (G : Type*) [Magma G] (h : Equation744 G) : Equation1594 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq20 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X2 ◇ X0))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq70 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq70 eq20


@[equational_result]
theorem Equation744_implies_Equation1603 (G : Type*) [Magma G] (h : Equation744 G) : Equation1603 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq20 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X2 ◇ X0))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq70 (X0 : G) : sK0 ≠ (X0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq70 eq20


@[equational_result]
theorem Equation744_implies_Equation1502 (G : Type*) [Magma G] (h : Equation744 G) : Equation1502 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq20 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X2 ◇ X0))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq70 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq70 eq20


@[equational_result]
theorem Equation744_implies_Equation930 (G : Type*) [Magma G] (h : Equation744 G) : Equation930 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq20 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X2 ◇ X0))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq62 (X0 : G) : sK0 ≠ (sK1 ◇ ((X0 ◇ sK2) ◇ (sK1 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.1 in 10
  subsumption eq62 eq20


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
theorem Equation989_implies_Equation926 (G : Type*) [Magma G] (h : Equation989 G) : Equation926 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ (X4 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X2 X3 X4 : G) : (X2 ◇ X3) = (X4 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK0 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  subsumption eq23 eq11


@[equational_result]
theorem Equation989_implies_Equation4155 (G : Type*) [Magma G] (h : Equation989 G) : Equation4155 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X2 X3 X4 : G) : (X2 ◇ X3) = (X4 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK1) ≠ (((X0 ◇ sK0) ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation989_implies_Equation1569 (G : Type*) [Magma G] (h : Equation989 G) : Equation1569 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ (X4 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X2 X3 X4 : G) : (X2 ◇ X3) = (X4 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 (X0 : G) : sK0 ≠ (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq23 eq11


@[equational_result]
theorem Equation989_implies_Equation4118 (G : Type*) [Magma G] (h : Equation989 G) : Equation4118 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X2 X3 X4 : G) : (X2 ◇ X3) = (X4 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK1) ≠ (((X0 ◇ sK0) ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation989_implies_Equation72 (G : Type*) [Magma G] (h : Equation989 G) : Equation72 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ (X4 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X2 X3 X4 : G) : (X2 ◇ X3) = (X4 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 : G) : sK0 ≠ (sK1 ◇ (sK1 ◇ (X0 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.2 in 10
  subsumption eq24 eq11


@[equational_result]
theorem Equation912_implies_Equation4619 (G : Type*) [Magma G] (h : Equation912 G) : Equation4619 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((X0 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq20 eq13


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
theorem Equation806_implies_Equation838 (G : Type*) [Magma G] (h : Equation806 G) : Equation838 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ (X2 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation806_implies_Equation1547 (G : Type*) [Magma G] (h : Equation806 G) : Equation1547 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq11 (X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ (X2 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation806_implies_Equation682 (G : Type*) [Magma G] (h : Equation806 G) : Equation682 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq11 (X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ (X2 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation806_implies_Equation1465 (G : Type*) [Magma G] (h : Equation806 G) : Equation1465 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ (X2 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation806_implies_Equation4635 (G : Type*) [Magma G] (h : Equation806 G) : Equation4635 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ (X2 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X2 X3 X4 : G) : ((X2 ◇ X2) ◇ X3) = (X4 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X2 X3 X4 : G) : (X4 ◇ X3) = (X2 ◇ X3) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq47 (X0 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq47 eq17


@[equational_result]
theorem Equation500_implies_Equation575 (G : Type*) [Magma G] (h : Equation500 G) : Equation575 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1 in 11
  have eq15 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.2 in 9
  have eq38 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK0)))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  have eq82 : sK0 ≠ sK0 := superpose eq15 eq38 -- superposition 38,15, 15 into 38, unify on (0).2 in 15 and (0).2 in 38
  subsumption eq82 rfl


@[equational_result]
theorem Equation500_implies_Equation528 (G : Type*) [Magma G] (h : Equation500 G) : Equation528 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq12 eq9


@[equational_result]
theorem Equation500_implies_Equation513 (G : Type*) [Magma G] (h : Equation500 G) : Equation513 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq12 eq9


@[equational_result]
theorem Equation500_implies_Equation419 (G : Type*) [Magma G] (h : Equation500 G) : Equation419 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq12 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq12 eq9


@[equational_result]
theorem Equation575_implies_Equation500 (G : Type*) [Magma G] (h : Equation575 G) : Equation500 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X3 ◇ (X3 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq30 (X0 : G) : sK0 ≠ (sK0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq30 eq9


@[equational_result]
theorem Equation463_implies_Equation4076 (G : Type*) [Magma G] (h : Equation463 G) : Equation4076 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq18 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq19 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ X0) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq20 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ X0) = (X1 ◇ X0) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq33 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq20 eq20 -- superposition 20,20, 20 into 20, unify on (0).2 in 20 and (0).1 in 20
  have eq56 (X0 : G) : (sK0 ◇ sK0) ≠ (((X0 ◇ sK1) ◇ sK2) ◇ sK0) := superpose eq33 eq10 -- superposition 10,33, 33 into 10, unify on (0).2 in 33 and (0).2.1.1 in 10
  subsumption eq56 eq33


@[equational_result]
theorem Equation463_implies_Equation4150 (G : Type*) [Magma G] (h : Equation463 G) : Equation4150 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK3) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq18 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq19 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ X0) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq20 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ X0) = (X1 ◇ X0) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq33 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq20 eq20 -- superposition 20,20, 20 into 20, unify on (0).2 in 20 and (0).1 in 20
  have eq56 (X0 : G) : (sK0 ◇ sK1) ≠ (((X0 ◇ sK2) ◇ sK3) ◇ sK1) := superpose eq33 eq10 -- superposition 10,33, 33 into 10, unify on (0).2 in 33 and (0).2.1.1 in 10
  subsumption eq56 eq33


@[equational_result]
theorem Equation463_implies_Equation416 (G : Type*) [Magma G] (h : Equation463 G) : Equation416 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq18 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq19 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ X0) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq20 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ X0) = (X1 ◇ X0) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq33 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq20 eq20 -- superposition 20,20, 20 into 20, unify on (0).2 in 20 and (0).1 in 20
  have eq61 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose eq33 eq9 -- superposition 9,33, 33 into 9, unify on (0).2 in 33 and (0).1.2.2 in 9
  have eq75 (X0 : G) : sK0 ≠ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := superpose eq33 eq10 -- superposition 10,33, 33 into 10, unify on (0).2 in 33 and (0).2 in 10
  subsumption eq75 eq61


@[equational_result]
theorem Equation463_implies_Equation491 (G : Type*) [Magma G] (h : Equation463 G) : Equation491 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) = (X1 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq13 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq17 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) = (X1 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ X0)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq19 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ X0) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq20 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ X0) = (X1 ◇ X0) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq33 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq20 eq20 -- superposition 20,20, 20 into 20, unify on (0).2 in 20 and (0).1 in 20
  have eq71 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X2 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) := superpose eq33 eq11 -- superposition 11,33, 33 into 11, unify on (0).2 in 33 and (0).2.2 in 11
  have eq73 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := superpose eq33 eq10 -- superposition 10,33, 33 into 10, unify on (0).2 in 33 and (0).2.2 in 10
  have eq117 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq20 eq17 -- superposition 17,20, 20 into 17, unify on (0).2 in 20 and (0).2.2 in 17
  have eq161 : sK0 ≠ (((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ (((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ (sK2 ◇ (sK2 ◇ sK0)))) := superpose eq17 eq73 -- superposition 73,17, 17 into 73, unify on (0).2 in 17 and (0).2 in 73
  have eq167 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1)))) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1)))) ◇ (X0 ◇ X1))) := superpose eq117 eq117 -- superposition 117,117, 117 into 117, unify on (0).2 in 117 and (0).1.1.2.2 in 117
  have eq225 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1))) := superpose eq117 eq167 -- forward demodulation 167,117
  have eq226 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1))) := superpose eq71 eq225 -- forward demodulation 225,71
  have eq227 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1))) := superpose eq9 eq226 -- forward demodulation 226,9
  have eq228 : sK0 ≠ (((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0)))) := superpose eq227 eq161 -- backward demodulation 161,227
  have eq229 : sK0 ≠ (((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq71 eq228 -- forward demodulation 228,71
  subsumption eq229 eq9


@[equational_result]
theorem Equation463_implies_Equation4316 (G : Type*) [Magma G] (h : Equation463 G) : Equation4316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq18 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ X0) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq33 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq20 eq20 -- superposition 20,20, 20 into 20, unify on (0).2 in 20 and (0).2 in 20
  have eq74 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq33 eq10 -- superposition 10,33, 33 into 10, unify on (0).2 in 33 and (0).2.2 in 10
  subsumption eq74 rfl


@[equational_result]
theorem Equation487_implies_Equation4200 (G : Type*) [Magma G] (h : Equation487 G) : Equation4200 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK0) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq30 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq36 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq30 eq30 -- superposition 30,30, 30 into 30, unify on (0).2 in 30 and (0).1.2 in 30
  have eq57 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ sK1) := superpose eq36 eq10 -- backward demodulation 10,36
  have eq94 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq36 eq57 -- superposition 57,36, 36 into 57, unify on (0).2 in 36 and (0).2 in 57
  subsumption eq94 eq36


@[equational_result]
theorem Equation487_implies_Equation4155 (G : Type*) [Magma G] (h : Equation487 G) : Equation4155 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq30 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq36 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq30 eq30 -- superposition 30,30, 30 into 30, unify on (0).2 in 30 and (0).1.2 in 30
  have eq57 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq36 eq10 -- backward demodulation 10,36
  have eq99 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq36 eq57 -- superposition 57,36, 36 into 57, unify on (0).2 in 36 and (0).2 in 57
  subsumption eq99 eq36


@[equational_result]
theorem Equation487_implies_Equation463 (G : Type*) [Magma G] (h : Equation487 G) : Equation463 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq30 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq49 : sK0 ≠ sK0 := superpose eq30 eq10 -- superposition 10,30, 30 into 10, unify on (0).2 in 30 and (0).2 in 10
  subsumption eq49 rfl


@[equational_result]
theorem Equation487_implies_Equation3993 (G : Type*) [Magma G] (h : Equation487 G) : Equation3993 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq30 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq36 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq30 eq30 -- superposition 30,30, 30 into 30, unify on (0).2 in 30 and (0).1.2 in 30
  have eq55 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := superpose eq36 eq12 -- backward demodulation 12,36
  have eq73 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := superpose eq55 eq10 -- backward demodulation 10,55
  have eq94 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq36 eq73 -- superposition 73,36, 36 into 73, unify on (0).2 in 36 and (0).2 in 73
  subsumption eq94 eq36


@[equational_result]
theorem Equation487_implies_Equation4327 (G : Type*) [Magma G] (h : Equation487 G) : Equation4327 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq30 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq36 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq30 eq30 -- superposition 30,30, 30 into 30, unify on (0).2 in 30 and (0).1.2 in 30
  have eq53 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := superpose eq36 eq12 -- backward demodulation 12,36
  have eq57 : (sK2 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq36 eq10 -- backward demodulation 10,36
  subsumption eq57 eq53


@[equational_result]
theorem Equation487_implies_Equation3909 (G : Type*) [Magma G] (h : Equation487 G) : Equation3909 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq30 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq36 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq30 eq30 -- superposition 30,30, 30 into 30, unify on (0).2 in 30 and (0).1.2 in 30
  have eq122 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq36 eq10 -- superposition 10,36, 36 into 10, unify on (0).2 in 36 and (0).2 in 10
  subsumption eq122 rfl


@[equational_result]
theorem Equation487_implies_Equation450 (G : Type*) [Magma G] (h : Equation487 G) : Equation450 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq30 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq36 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq30 eq30 -- superposition 30,30, 30 into 30, unify on (0).2 in 30 and (0).1.2 in 30
  have eq53 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := superpose eq36 eq12 -- backward demodulation 12,36
  have eq57 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := superpose eq36 eq10 -- backward demodulation 10,36
  have eq82 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq53 eq57 -- forward demodulation 57,53
  have eq95 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq36 eq36 -- superposition 36,36, 36 into 36, unify on (0).2 in 36 and (0).2 in 36
  have eq162 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose eq95 eq30 -- superposition 30,95, 95 into 30, unify on (0).2 in 95 and (0).1.2 in 30
  have eq170 (X0 : G) : sK0 ≠ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq95 eq82 -- superposition 82,95, 95 into 82, unify on (0).2 in 95 and (0).2 in 82
  subsumption eq170 eq162


@[equational_result]
theorem Equation520_implies_Equation4067 (G : Type*) [Magma G] (h : Equation520 G) : Equation4067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation520_implies_Equation454 (G : Type*) [Magma G] (h : Equation520 G) : Equation454 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq14 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X2 := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1 in 14
  have eq38 (X0 : G) : sK0 ≠ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := superpose eq14 eq13 -- superposition 13,14, 14 into 13, unify on (0).2 in 14 and (0).2 in 13
  subsumption eq38 eq21


@[equational_result]
theorem Equation520_implies_Equation4192 (G : Type*) [Magma G] (h : Equation520 G) : Equation4192 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq14 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2 in 12
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.1 in 13
  subsumption eq20 eq14


@[equational_result]
theorem Equation520_implies_Equation3947 (G : Type*) [Magma G] (h : Equation520 G) : Equation3947 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK3)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 eq12


@[equational_result]
theorem Equation520_implies_Equation4118 (G : Type*) [Magma G] (h : Equation520 G) : Equation4118 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2 in 12
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.1 in 13
  subsumption eq20 eq14


@[equational_result]
theorem Equation520_implies_Equation4606 (G : Type*) [Magma G] (h : Equation520 G) : Equation4606 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : ((sK0 ◇ sK0) ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation520_implies_Equation3880 (G : Type*) [Magma G] (h : Equation520 G) : Equation3880 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation520_implies_Equation3887 (G : Type*) [Magma G] (h : Equation520 G) : Equation3887 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation520_implies_Equation375 (G : Type*) [Magma G] (h : Equation520 G) : Equation375 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq14 eq12


@[equational_result]
theorem Equation520_implies_Equation487 (G : Type*) [Magma G] (h : Equation520 G) : Equation487 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X2 := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1 in 14
  have eq38 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := superpose eq14 eq13 -- superposition 13,14, 14 into 13, unify on (0).2 in 14 and (0).2.2 in 13
  subsumption eq38 eq21


@[equational_result]
theorem Equation520_implies_Equation3877 (G : Type*) [Magma G] (h : Equation520 G) : Equation3877 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation520_implies_Equation4001 (G : Type*) [Magma G] (h : Equation520 G) : Equation4001 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK0 ◇ sK3)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 eq12


@[equational_result]
theorem Equation520_implies_Equation4226 (G : Type*) [Magma G] (h : Equation520 G) : Equation4226 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK2) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2 in 12
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.1 in 13
  subsumption eq20 eq14


@[equational_result]
theorem Equation520_implies_Equation4165 (G : Type*) [Magma G] (h : Equation520 G) : Equation4165 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2 in 12
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.1 in 13
  subsumption eq20 eq14


@[equational_result]
theorem Equation520_implies_Equation4073 (G : Type*) [Magma G] (h : Equation520 G) : Equation4073 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation571_implies_Equation3921 (G : Type*) [Magma G] (h : Equation571 G) : Equation3921 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq19 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq19 eq14


@[equational_result]
theorem Equation571_implies_Equation4677 (G : Type*) [Magma G] (h : Equation571 G) : Equation4677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK1 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : ((sK0 ◇ sK1) ◇ sK2) ≠ (sK2 ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation571_implies_Equation473 (G : Type*) [Magma G] (h : Equation571 G) : Equation473 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (X0 ◇ sK0)))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2.2.2 in 10
  have eq117 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).2.2 in 16
  subsumption eq117 eq9


@[equational_result]
theorem Equation571_implies_Equation3997 (G : Type*) [Magma G] (h : Equation571 G) : Equation3997 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK0 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq21 eq14


@[equational_result]
theorem Equation571_implies_Equation3905 (G : Type*) [Magma G] (h : Equation571 G) : Equation3905 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation571_implies_Equation3873 (G : Type*) [Magma G] (h : Equation571 G) : Equation3873 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq21 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation571_implies_Equation520 (G : Type*) [Magma G] (h : Equation571 G) : Equation520 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq82 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))) = X1 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2.2 in 9
  have eq91 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2 in 10
  subsumption eq91 eq82


@[equational_result]
theorem Equation571_implies_Equation4351 (G : Type*) [Magma G] (h : Equation571 G) : Equation4351 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq16 (X0 : G) : (sK0 ◇ (X0 ◇ sK1)) ≠ (sK2 ◇ (X0 ◇ sK1)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).1.2 in 10
  subsumption eq16 eq14


@[equational_result]
theorem Equation571_implies_Equation503 (G : Type*) [Magma G] (h : Equation571 G) : Equation503 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq35 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))) = X1 := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).1.2.2 in 9
  have eq40 (X0 : G) : sK0 ≠ (sK1 ◇ (sK1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.2.2 in 13
  subsumption eq40 eq35


@[equational_result]
theorem Equation571_implies_Equation4104 (G : Type*) [Magma G] (h : Equation571 G) : Equation4104 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation491_implies_Equation3915 (G : Type*) [Magma G] (h : Equation491 G) : Equation3915 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1 in 13
  have eq18 (X0 : G) : (sK0 ◇ sK1) ≠ ((sK0 ◇ (X0 ◇ sK0)) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.2 in 10
  subsumption eq18 eq16


@[equational_result]
theorem Equation491_implies_Equation545 (G : Type*) [Magma G] (h : Equation491 G) : Equation545 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq37 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.2 in 9
  have eq42 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).2 in 15
  subsumption eq42 eq37


@[equational_result]
theorem Equation491_implies_Equation3883 (G : Type*) [Magma G] (h : Equation491 G) : Equation3883 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation491_implies_Equation571 (G : Type*) [Magma G] (h : Equation491 G) : Equation571 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X1))) = (X3 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq13 eq12 -- backward demodulation 12,13
  have eq42 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (X0 ◇ (X0 ◇ sK0)))) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2.2 in 10
  have eq181 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ (X0 ◇ (X0 ◇ sK0)))) := superpose eq11 eq42 -- superposition 42,11, 11 into 42, unify on (0).2 in 11 and (0).2.2 in 42
  subsumption eq181 eq9


@[equational_result]
theorem Equation491_implies_Equation4083 (G : Type*) [Magma G] (h : Equation491 G) : Equation4083 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation491_implies_Equation4635 (G : Type*) [Magma G] (h : Equation491 G) : Equation4635 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation491_implies_Equation4112 (G : Type*) [Magma G] (h : Equation491 G) : Equation4112 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK3) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK0) ≠ ((sK3 ◇ sK3) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation491_implies_Equation4158 (G : Type*) [Magma G] (h : Equation491 G) : Equation4158 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq23 (X0 : G) : (sK0 ◇ sK1) ≠ ((X0 ◇ sK1) ◇ sK1) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.1 in 14
  subsumption eq23 eq18


@[equational_result]
theorem Equation491_implies_Equation4619 (G : Type*) [Magma G] (h : Equation491 G) : Equation4619 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : ((sK0 ◇ sK0) ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation491_implies_Equation3901 (G : Type*) [Magma G] (h : Equation491 G) : Equation3901 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation491_implies_Equation3870 (G : Type*) [Magma G] (h : Equation491 G) : Equation3870 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq23 rfl


@[equational_result]
theorem Equation491_implies_Equation4291 (G : Type*) [Magma G] (h : Equation491 G) : Equation4291 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq60 (X0 : G) : (sK0 ◇ (X0 ◇ sK1)) ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).1.2 in 10
  subsumption eq60 eq17


@[equational_result]
theorem Equation491_implies_Equation381 (G : Type*) [Magma G] (h : Equation491 G) : Equation381 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 eq13


@[equational_result]
theorem Equation491_implies_Equation4378 (G : Type*) [Magma G] (h : Equation491 G) : Equation4378 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK4 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := superpose eq13 eq12 -- backward demodulation 12,13
  have eq15 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK2 ◇ sK2)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq64 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2.2 in 14
  have eq84 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (X0 ◇ sK2)) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2 in 15
  subsumption eq84 eq64


@[equational_result]
theorem Equation491_implies_Equation361 (G : Type*) [Magma G] (h : Equation491 G) : Equation361 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation491_implies_Equation39 (G : Type*) [Magma G] (h : Equation491 G) : Equation39 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation491_implies_Equation4108 (G : Type*) [Magma G] (h : Equation491 G) : Equation4108 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : (sK0 ◇ sK0) ≠ ((sK2 ◇ sK2) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation491_implies_Equation3955 (G : Type*) [Magma G] (h : Equation491 G) : Equation3955 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation491_implies_Equation3943 (G : Type*) [Magma G] (h : Equation491 G) : Equation3943 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation491_implies_Equation4611 (G : Type*) [Magma G] (h : Equation491 G) : Equation4611 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : ((sK0 ◇ sK0) ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation1184_implies_Equation1949 (G : Type*) [Magma G] (h : Equation1184 G) : Equation1949 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq36 (X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X3)) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq69 : sK0 ≠ sK0 := superpose eq36 eq10 -- superposition 10,36, 36 into 10, unify on (0).2 in 36 and (0).2 in 10
  subsumption eq69 rfl


@[equational_result]
theorem Equation1184_implies_Equation1921 (G : Type*) [Magma G] (h : Equation1184 G) : Equation1921 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq36 (X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X3)) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq69 : sK0 ≠ sK0 := superpose eq36 eq10 -- superposition 10,36, 36 into 10, unify on (0).2 in 36 and (0).2 in 10
  subsumption eq69 rfl


@[equational_result]
theorem Equation1184_implies_Equation1840 (G : Type*) [Magma G] (h : Equation1184 G) : Equation1840 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq36 (X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X3)) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq69 : sK0 ≠ sK0 := superpose eq36 eq10 -- superposition 10,36, 36 into 10, unify on (0).2 in 36 and (0).2 in 10
  subsumption eq69 rfl


@[equational_result]
theorem Equation1949_implies_Equation1184 (G : Type*) [Magma G] (h : Equation1949 G) : Equation1184 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq76 : sK0 ≠ sK0 := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq76 rfl


@[equational_result]
theorem Equation1949_implies_Equation1045 (G : Type*) [Magma G] (h : Equation1949 G) : Equation1045 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq76 : sK0 ≠ sK0 := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq76 rfl


@[equational_result]
theorem Equation1949_implies_Equation1075 (G : Type*) [Magma G] (h : Equation1949 G) : Equation1075 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq76 : sK0 ≠ sK0 := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq76 rfl


@[equational_result]
theorem Equation1167_implies_Equation2000 (G : Type*) [Magma G] (h : Equation1167 G) : Equation2000 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) = X2 := superpose eq18 eq11 -- backward demodulation 11,18
  have eq27 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq27 rfl


@[equational_result]
theorem Equation1167_implies_Equation1949 (G : Type*) [Magma G] (h : Equation1167 G) : Equation1949 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq20 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : sK0 ≠ (sK2 ◇ (sK2 ◇ sK0)) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq22 eq20


@[equational_result]
theorem Equation1167_implies_Equation3887 (G : Type*) [Magma G] (h : Equation1167 G) : Equation3887 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq20 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq22 rfl


@[equational_result]
theorem Equation1167_implies_Equation3952 (G : Type*) [Magma G] (h : Equation1167 G) : Equation3952 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq65 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq65 rfl


@[equational_result]
theorem Equation1167_implies_Equation3414 (G : Type*) [Magma G] (h : Equation1167 G) : Equation3414 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq20 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation1167_implies_Equation3278 (G : Type*) [Magma G] (h : Equation1167 G) : Equation3278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq20 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation1167_implies_Equation500 (G : Type*) [Magma G] (h : Equation1167 G) : Equation500 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq20 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq22 eq20


@[equational_result]
theorem Equation1167_implies_Equation1884 (G : Type*) [Magma G] (h : Equation1167 G) : Equation1884 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) = X2 := superpose eq18 eq11 -- backward demodulation 11,18
  have eq27 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq27 rfl


@[equational_result]
theorem Equation1167_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1167 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq14 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2 in 10
  have eq17 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq11 eq14 -- forward demodulation 14,11
  have eq19 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq17 eq8 -- backward demodulation 8,17
  have eq21 : sK0 ≠ sK0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2 in 9
  subsumption eq21 rfl


@[equational_result]
theorem Equation1167_implies_Equation3877 (G : Type*) [Magma G] (h : Equation1167 G) : Equation3877 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq65 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq65 rfl


@[equational_result]
theorem Equation1167_implies_Equation3353 (G : Type*) [Magma G] (h : Equation1167 G) : Equation3353 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq20 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq22 rfl


